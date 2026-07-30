use crate::ir::{
    SemanticExpression, SemanticLoopKind, SemanticNode, SemanticOperand, SemanticPredicate,
    SemanticStatement,
};

use super::super::effects::EffectSummary;
use super::{FlowCollector, FlowTask, UseSite};
use crate::analysis::value_recovery::{domain::ControlDomain, ValueRecoveryError};

pub(super) struct NodeScheduler<'collector, 'node> {
    collector: &'collector mut FlowCollector<'node>,
    domain: ControlDomain,
    pending: &'collector mut Vec<FlowTask<'node>>,
}

impl<'collector, 'node> NodeScheduler<'collector, 'node> {
    pub(super) fn new(
        collector: &'collector mut FlowCollector<'node>,
        domain: ControlDomain,
        pending: &'collector mut Vec<FlowTask<'node>>,
    ) -> Self {
        Self {
            collector,
            domain,
            pending,
        }
    }

    pub(super) fn schedule(&mut self, node: &'node SemanticNode) -> Result<(), ValueRecoveryError> {
        match node {
            SemanticNode::Empty => {}
            SemanticNode::BasicBlock(block) => {
                self.collector.record_block(block.id, self.domain)?;
                self.pending.extend(
                    block
                        .statements
                        .iter()
                        .rev()
                        .map(|statement| FlowTask::Statement(statement, self.domain)),
                );
            }
            SemanticNode::Sequence(children) => self.schedule_sequence(children)?,
            SemanticNode::If {
                condition,
                then_node,
                else_node,
            } => self.schedule_if(condition, then_node, else_node.as_deref())?,
            SemanticNode::Loop {
                kind, test, body, ..
            } => self.schedule_loop(*kind, &test.setup, &test.condition, body)?,
            SemanticNode::For {
                init,
                condition,
                update,
                body,
                ..
            } => self.schedule_for(init, condition, update, body)?,
            SemanticNode::ForEach {
                variable,
                iterable,
                body,
                ..
            } => self.schedule_foreach(variable, iterable, body)?,
            SemanticNode::Switch {
                selector, cases, ..
            } => self.schedule_switch(selector, cases)?,
            SemanticNode::Try {
                body,
                catches,
                finally,
                ..
            } => self.schedule_protection(body, catches, finally.as_ref()),
            SemanticNode::Synchronized { lock, body, .. } => {
                self.schedule_synchronized(lock, body)?
            }
            SemanticNode::Label { body, .. } => self.push_scoped(body, self.domain, false),
            SemanticNode::Leave(leave) => self.schedule_leave(leave)?,
        }
        Ok(())
    }

    fn schedule_sequence(
        &mut self,
        children: &'node [SemanticNode],
    ) -> Result<(), ValueRecoveryError> {
        let mut domain = self.domain;
        let mut scheduled = Vec::with_capacity(children.len());
        for child in children {
            scheduled.push((child, domain));
            let fallthrough = self.collector.fallthrough_domain(child)?;
            domain = self.collector.graph.logic.and(domain, fallthrough)?;
        }
        self.pending.extend(
            scheduled
                .into_iter()
                .rev()
                .map(|(child, domain)| FlowTask::Node(child, domain)),
        );
        Ok(())
    }

    fn schedule_if(
        &mut self,
        condition: &'node SemanticOperand<SemanticPredicate>,
        then_node: &'node SemanticNode,
        else_node: Option<&'node SemanticNode>,
    ) -> Result<(), ValueRecoveryError> {
        self.record_predicate(condition, condition.site.map(UseSite::Predicate))?;
        let condition_domain = self.collector.graph.logic.compile(&condition.domain()?)?;
        if let Some(else_node) = else_node {
            let otherwise = self.collector.graph.logic.not(condition_domain)?;
            let domain = self.collector.graph.logic.and(self.domain, otherwise)?;
            self.push_scoped(else_node, domain, false);
        }
        let domain = self
            .collector
            .graph
            .logic
            .and(self.domain, condition_domain)?;
        self.push_scoped(then_node, domain, false);
        Ok(())
    }

    fn schedule_loop(
        &mut self,
        kind: SemanticLoopKind,
        setup: &'node SemanticNode,
        condition: &'node SemanticOperand<SemanticPredicate>,
        body: &'node SemanticNode,
    ) -> Result<(), ValueRecoveryError> {
        let condition_domain = self.collector.graph.logic.compile(&condition.domain()?)?;
        let body_domain = match kind {
            SemanticLoopKind::PreTested => self
                .collector
                .graph
                .logic
                .and(self.domain, condition_domain)?,
            SemanticLoopKind::PostTested | SemanticLoopKind::Endless => self.domain,
        };
        self.pending.push(FlowTask::LeaveScope(true));
        match kind {
            SemanticLoopKind::PreTested => {
                self.pending.push(FlowTask::Node(body, body_domain));
                self.pending.push(FlowTask::Predicate(
                    condition,
                    self.domain,
                    condition.site.map(UseSite::Predicate),
                ));
                self.pending.push(FlowTask::Node(setup, self.domain));
            }
            SemanticLoopKind::PostTested => {
                self.pending.push(FlowTask::Predicate(
                    condition,
                    self.domain,
                    condition.site.map(UseSite::Predicate),
                ));
                self.pending.push(FlowTask::Node(setup, self.domain));
                self.pending.push(FlowTask::Node(body, body_domain));
            }
            SemanticLoopKind::Endless => {
                self.pending.push(FlowTask::Node(body, body_domain));
                self.pending.push(FlowTask::Node(setup, self.domain));
            }
        }
        self.pending.push(FlowTask::EnterScope(true));
        Ok(())
    }

    fn schedule_for(
        &mut self,
        init: &'node SemanticStatement,
        condition: &'node SemanticOperand<SemanticPredicate>,
        update: &'node SemanticStatement,
        body: &'node SemanticNode,
    ) -> Result<(), ValueRecoveryError> {
        self.collector.visit_statement(init, self.domain)?;
        self.record_predicate(condition, condition.site.map(UseSite::Predicate))?;
        let condition_domain = self.collector.graph.logic.compile(&condition.domain()?)?;
        let iteration = self
            .collector
            .graph
            .logic
            .and(self.domain, condition_domain)?;
        self.pending.push(FlowTask::LeaveScope(true));
        self.pending.push(FlowTask::Statement(update, iteration));
        self.pending.push(FlowTask::Node(body, iteration));
        self.pending.push(FlowTask::EnterScope(true));
        Ok(())
    }

    fn schedule_foreach(
        &mut self,
        variable: &'node crate::ir::RegisterArg,
        iterable: &'node SemanticOperand<SemanticExpression>,
        body: &'node SemanticNode,
    ) -> Result<(), ValueRecoveryError> {
        self.collector.graph.record_binding(variable);
        let event = self.collector.event();
        let site = iterable.site.map(UseSite::Argument);
        let point = site.map(UseSite::before);
        let effect = self.collector.visit_expression_uses(
            iterable,
            self.domain,
            event,
            site,
            point.as_ref(),
        )?;
        self.collector
            .record_effect(iterable.site, self.domain, effect);
        self.push_scoped(body, self.domain, true);
        Ok(())
    }

    fn schedule_switch(
        &mut self,
        selector: &'node SemanticOperand<SemanticExpression>,
        cases: &'node [crate::ir::SemanticSwitchCase],
    ) -> Result<(), ValueRecoveryError> {
        let event = self.collector.event();
        let site = selector.site.map(UseSite::Argument);
        let point = site.map(UseSite::before);
        let effect = self.collector.visit_expression_uses(
            selector,
            self.domain,
            event,
            site,
            point.as_ref(),
        )?;
        self.collector
            .record_effect(selector.site, self.domain, effect);
        for case in cases.iter().rev() {
            self.push_scoped(&case.body, self.domain, false);
        }
        Ok(())
    }

    fn schedule_protection(
        &mut self,
        body: &'node SemanticNode,
        catches: &'node [crate::ir::SemanticCatch],
        finally: Option<&'node crate::ir::SemanticFinally>,
    ) {
        let protection = self.collector.protection();
        if let Some(finally) = finally {
            self.push_protected(&finally.body, protection);
        }
        for catch in catches.iter().rev() {
            if let Some(value) = catch.exception_value.as_ref() {
                self.collector.graph.record_binding(value);
            }
            self.push_protected(&catch.body, protection);
        }
        self.push_protected(body, protection);
    }

    fn schedule_synchronized(
        &mut self,
        lock: &'node SemanticOperand<SemanticExpression>,
        body: &'node SemanticNode,
    ) -> Result<(), ValueRecoveryError> {
        let event = self.collector.event();
        let site = lock.site.map(UseSite::Argument);
        let point = site.map(UseSite::before);
        let effect = self
            .collector
            .visit_expression_uses(lock, self.domain, event, site, point.as_ref())?
            .join(EffectSummary::synchronization());
        self.collector.record_effect(lock.site, self.domain, effect);
        let protection = self.collector.protection();
        self.push_protected(body, protection);
        Ok(())
    }

    fn schedule_leave(
        &mut self,
        leave: &'node crate::ir::SemanticLeave,
    ) -> Result<(), ValueRecoveryError> {
        let event = self.collector.event();
        let effect = if let Some(value) = leave.value() {
            let site = leave.site.map(super::UseSite::Leave);
            let origin = site.map(super::UseSite::before);
            self.collector.visit_leave_uses(
                value,
                leave.condition.as_ref(),
                self.domain,
                event,
                site,
                origin.as_ref(),
            )?
        } else {
            EffectSummary::pure()
        };
        self.collector
            .record_effect(leave.site, self.domain, effect);
        Ok(())
    }

    fn record_predicate(
        &mut self,
        predicate: &SemanticPredicate,
        site: Option<UseSite>,
    ) -> Result<(), ValueRecoveryError> {
        let event = self.collector.event();
        let point = site.map(UseSite::before);
        let effect = self.collector.visit_predicate_uses(
            predicate,
            self.domain,
            event,
            site,
            point.as_ref(),
        )?;
        self.collector
            .record_effect(site.map(UseSite::id), self.domain, effect);
        Ok(())
    }

    fn push_scoped(&mut self, node: &'node SemanticNode, domain: ControlDomain, repetitive: bool) {
        self.pending.push(FlowTask::LeaveScope(repetitive));
        self.pending.push(FlowTask::Node(node, domain));
        self.pending.push(FlowTask::EnterScope(repetitive));
    }

    fn push_protected(&mut self, node: &'node SemanticNode, protection: u32) {
        self.pending.push(FlowTask::LeaveProtection(protection));
        self.push_scoped(node, self.domain, false);
        self.pending.push(FlowTask::EnterProtection(protection));
    }
}
