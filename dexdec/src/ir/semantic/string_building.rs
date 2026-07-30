//! Recovery of string building that the compiler spread over several statements.
//!
//! `a + b` compiles to a `StringBuilder` allocated into a local, appended to
//! once per term, and read back with `toString`. Read literally that is one
//! variable and one statement per term, none of which the author wrote, and it
//! hides the concatenation from the proof that would fold it back: that proof
//! matches a chain of calls, and a builder living in a local is not one.
//!
//! `append` answers with the builder it was called on, so the statements are
//! already a chain — the compiler merely spelled it out a call at a time.
//! Writing it back as one expression is therefore an identity, not a guess:
//! the terms keep their order, nothing moves across a foreign statement, and
//! the builder still ends up in the same variable. What the chain then enables
//! is left to the stages that already exist — scheduling carries a
//! single-use builder to its `toString`, and the concatenation proof folds the
//! result into `+`.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{ArgType, InsnType, MemberReference, MethodReference, PrimitiveType, RegisterArg};

use super::{
    SemanticExpression, SemanticExpressionFacts, SemanticFoldError, SemanticFolder, SemanticNode,
    SemanticOperation, SemanticStatement, SemanticStatementKind, SemanticVisitor,
};

/// What `StringBuilder` and `StringBuffer` promise about their own calls.
///
/// Both languages recover concatenation from the same protocol, so the facts
/// about it are stated once here rather than per language.
pub struct StringBuilderProtocol;

impl StringBuilderProtocol {
    /// Whether the type is a builder whose protocol this module describes.
    pub fn is_builder(owner: &ArgType) -> bool {
        *owner == ArgType::object("java/lang/StringBuilder")
            || *owner == ArgType::object("java/lang/StringBuffer")
    }

    pub fn method(operation: &SemanticOperation) -> Option<&MethodReference> {
        let MemberReference::Method(method) = operation.payload.reference.as_ref()? else {
            return None;
        };
        Some(method)
    }

    /// The builder allocated by the operation, if that is what it does.
    fn allocation(operation: &SemanticOperation) -> Option<&MethodReference> {
        let method = Self::method(operation)?;
        (operation.insn_type == InsnType::Constructor
            && method.is_constructor()
            && Self::is_builder(&method.owner)
            && method.descriptor.return_type == ArgType::VOID
            && operation.operands().len() == method.descriptor.parameters.len() + 1)
            .then_some(method)
    }

    /// The append the operation performs on `owner`, if that is what it does.
    ///
    /// An append answers with its own receiver, which is what lets a run of
    /// them be written as a chain. The overloads taking `char[]` or a
    /// `CharSequence` range are left out: they do not agree with `+` on what
    /// they append.
    fn append<'a>(
        operation: &'a SemanticOperation,
        owner: &ArgType,
    ) -> Option<&'a MethodReference> {
        let method = Self::method(operation)?;
        (operation.insn_type == InsnType::Invoke
            && method.name == "append"
            && method.owner == *owner
            && operation.operands().len() == 2
            && Self::appendable(method, owner))
        .then_some(method)
    }

    fn appendable(method: &MethodReference, owner: &ArgType) -> bool {
        let [parameter] = method.descriptor.parameters.as_slice() else {
            return false;
        };
        Self::concatenable(parameter) && method.descriptor.return_type == *owner
    }

    /// Whether `+` would render the value the same way `append` does.
    fn concatenable(parameter: &ArgType) -> bool {
        matches!(
            parameter,
            ArgType::Primitive(
                PrimitiveType::Boolean
                    | PrimitiveType::Char
                    | PrimitiveType::Int
                    | PrimitiveType::Long
                    | PrimitiveType::Float
                    | PrimitiveType::Double
            )
        ) || matches!(
            parameter.as_object(),
            Some("java/lang/String" | "java/lang/Object")
        )
    }

    /// The terms a builder chain concatenates, in order.
    ///
    /// Answers only for a complete chain: a `toString` reading a run of
    /// appends that bottoms out at the allocation of the builder itself.
    pub fn terms(expression: &SemanticOperation) -> Option<Vec<SemanticExpression>> {
        let terminal = Self::method(expression)?;
        (expression.insn_type == InsnType::Invoke
            && terminal.name == "toString"
            && terminal.descriptor.parameters.is_empty()
            && terminal.descriptor.return_type == ArgType::object("java/lang/String")
            && Self::is_builder(&terminal.owner))
        .then_some(())?;
        let owner = &terminal.owner;
        let mut current = expression.operands().first()?.as_operation()?;
        let mut appended = Vec::new();
        let seed = loop {
            if let Some(method) = Self::append(current, owner) {
                appended.push((
                    current.operands()[1].clone(),
                    method.descriptor.parameters[0].clone(),
                ));
                current = current.operands()[0].as_operation()?;
                continue;
            }
            break Self::seed(current, owner)?;
        };
        appended.reverse();
        // `+` starts from a string, so a chain that does not already begin with
        // one needs an empty string to give the sum its type.
        let leads_with_string = seed.is_some()
            || appended
                .first()
                .is_some_and(|(_, parameter)| parameter == &ArgType::string());
        let mut terms = (!leads_with_string)
            .then(Self::empty_string)
            .into_iter()
            .chain(seed)
            .collect::<Vec<_>>();
        terms.extend(
            appended
                .into_iter()
                .map(|(value, parameter)| Self::declared(value, &parameter)),
        );
        Some(terms)
    }

    /// The term restated at the type its call declared for it.
    ///
    /// A `char` or a `boolean` reaches an append as an integer constant, and
    /// only the parameter it is passed as tells it apart from one. Folding the
    /// call away takes that parameter with it, so the type has to move onto the
    /// value first or `']'` comes back as 93.
    ///
    /// Anything but a constant carries its own type already: a narrowing of
    /// something wider is a conversion in its own right, and survives the fold.
    fn declared(value: SemanticExpression, parameter: &ArgType) -> SemanticExpression {
        if !matches!(parameter, ArgType::Primitive(_)) {
            return value;
        }
        match value {
            SemanticExpression::Literal(mut literal) => {
                literal.ty = parameter.clone();
                SemanticExpression::Literal(literal)
            }
            SemanticExpression::Operation(mut operation)
                if operation.insn_type == InsnType::Const =>
            {
                if let Some(result) = operation.result.as_mut() {
                    result.ty = parameter.clone();
                }
                if let [SemanticExpression::Literal(literal)] = operation.operands_mut() {
                    literal.ty = parameter.clone();
                }
                SemanticExpression::Operation(operation)
            }
            value => value,
        }
    }

    /// The term a builder's own allocation contributes, if any.
    ///
    /// A capacity contributes nothing — it cannot be observed through the
    /// string. A starting string contributes itself, but only when it is a
    /// literal: `StringBuilder(null)` raises where `null + x` reads "null", so
    /// the two agree only where the argument is known not to be null.
    fn seed(operation: &SemanticOperation, owner: &ArgType) -> Option<Option<SemanticExpression>> {
        let method = Self::allocation(operation)?;
        (method.owner == *owner).then_some(())?;
        match method.descriptor.parameters.as_slice() {
            [] => Some(None),
            [ArgType::Primitive(PrimitiveType::Int)] => Some(None),
            [parameter] if parameter.as_object() == Some("java/lang/String") => {
                let argument = operation.operands().get(1)?;
                Self::is_string_literal(argument).then(|| Some(argument.clone()))
            }
            _ => None,
        }
    }

    fn is_string_literal(expression: &SemanticExpression) -> bool {
        expression
            .as_operation()
            .is_some_and(|operation| operation.insn_type == InsnType::ConstStr)
    }

    fn empty_string() -> SemanticExpression {
        SemanticExpression::Operation(Box::new(SemanticOperation::string_literal(String::new())))
    }
}

/// One value, named the way this stage can still tell values apart.
type ValueKey = (u32, Option<u32>, Option<u32>);

/// How a method reads each of its builders.
///
/// A builder worth rewriting is one the method fills and then reads back as a
/// string, and does nothing else with. One handed to something else, or still
/// being appended to further down, is being used as a builder — the appends
/// are not spelling out a concatenation, and merging some of them would only
/// move the seam.
#[derive(Default)]
struct BuilderReads {
    reads: BTreeMap<ValueKey, usize>,
    read_back: BTreeSet<ValueKey>,
}

impl BuilderReads {
    fn key(register: &RegisterArg) -> ValueKey {
        (register.reg_num, register.ssa_version, register.code_var)
    }

    fn of(root: &SemanticNode) -> Self {
        let mut builders = Self::default();
        builders.visit_node(root);
        builders
    }

    /// Whether merging this many appends leaves the builder read exactly once,
    /// by the `toString` the appends were building towards.
    ///
    /// Every read is accounted for: the allocation names the object it is
    /// initialising, each append names the builder it answers with, and the
    /// read-back is the one that has to survive.
    fn completed_by(&self, builder: &RegisterArg, appended: usize) -> bool {
        let key = Self::key(builder);
        self.read_back.contains(&key) && self.reads.get(&key).copied().unwrap_or(0) == appended + 2
    }
}

impl SemanticVisitor for BuilderReads {
    fn visit_register(&mut self, register: &RegisterArg) {
        *self.reads.entry(Self::key(register)).or_default() += 1;
    }

    fn enter_operation(&mut self, operation: &SemanticOperation) {
        let Some(method) = StringBuilderProtocol::method(operation) else {
            return;
        };
        if operation.insn_type != InsnType::Invoke
            || method.name != "toString"
            || !StringBuilderProtocol::is_builder(&method.owner)
        {
            return;
        }
        let receiver = operation
            .operands()
            .first()
            .and_then(|operand| operand.as_register());
        if let Some(receiver) = receiver {
            self.read_back.insert(Self::key(receiver));
        }
    }
}

/// Merges each builder's own appends into the statement that allocates it.
pub struct StringBuildingRecovery {
    builders: BuilderReads,
    changed: bool,
}

impl StringBuildingRecovery {
    pub fn apply(root: &mut SemanticNode) -> Result<bool, SemanticFoldError> {
        let mut recovery = Self {
            builders: BuilderReads::of(root),
            changed: false,
        };
        if recovery.builders.read_back.is_empty() {
            return Ok(false);
        }
        let body = std::mem::replace(root, SemanticNode::Empty);
        *root = recovery.fold_node(body)?;
        Ok(recovery.changed)
    }

    fn merge(&self, statements: &mut Vec<SemanticStatement>) -> bool {
        let mut changed = false;
        let mut index = 0;
        while index < statements.len() {
            let Some(builder) = Self::allocated_builder(&statements[index]) else {
                index += 1;
                continue;
            };
            let appended = Self::run_length(&statements[index + 1..], &builder);
            if appended == 0 || !self.builders.completed_by(&builder, appended) {
                index += 1;
                continue;
            }
            let appends = statements
                .drain(index + 1..index + 1 + appended)
                .collect::<Vec<_>>();
            Self::chain(&mut statements[index], appends);
            changed = true;
            index += 1;
        }
        changed
    }

    /// The builder the statement allocates, if that is what it does.
    fn allocated_builder(statement: &SemanticStatement) -> Option<RegisterArg> {
        let operation = statement.instruction_ref()?;
        StringBuilderProtocol::allocation(operation)?;
        operation.result.clone()
    }

    /// How many of the statements that follow append to this builder and
    /// nothing else.
    ///
    /// The run stops at the first statement that is anything else, so no
    /// statement is ever moved across another and the terms keep both their
    /// order and their neighbours.
    fn run_length(statements: &[SemanticStatement], builder: &RegisterArg) -> usize {
        statements
            .iter()
            .take_while(|statement| Self::appends_to(statement, builder))
            .count()
    }

    fn appends_to(statement: &SemanticStatement, builder: &RegisterArg) -> bool {
        let Some(operation) = statement.instruction_ref() else {
            return false;
        };
        // A statement that keeps the answer is already a chain of its own, and
        // one that reads the builder to build its own argument would read it
        // before the merged statement defines it.
        operation.result.is_none()
            && StringBuilderProtocol::append(operation, &builder.ty).is_some()
            && operation.operands()[0]
                .as_register()
                .is_some_and(|receiver| Self::same_value(receiver, builder))
            && !SemanticExpressionFacts::of_expression(&operation.operands()[1])
                .uses(builder.reg_num)
    }

    fn same_value(register: &RegisterArg, builder: &RegisterArg) -> bool {
        register.reg_num == builder.reg_num
            && register.ssa_version == builder.ssa_version
            && register.code_var == builder.code_var
    }

    /// Rewrites the allocation into the chain that its appends spell out.
    ///
    /// The last append answers with the builder, so it carries the definition
    /// the allocation used to make; the ones it swallows stop being statements
    /// and become the receiver of the next.
    fn chain(allocation: &mut SemanticStatement, appends: Vec<SemanticStatement>) {
        let SemanticStatementKind::Instruction(construction) = &allocation.kind else {
            return;
        };
        let mut chain: Option<SemanticOperation> = None;
        for append in appends {
            let SemanticStatementKind::Instruction(mut operation) = append.kind else {
                continue;
            };
            let receiver = chain.take().unwrap_or_else(|| {
                let mut construction = construction.clone();
                // The allocation stops being a definition of its own: the value
                // it makes now reaches the variable through the chain.
                construction.discard_result();
                construction
            });
            operation.operands_mut()[0] = SemanticExpression::Operation(Box::new(receiver));
            chain = Some(operation);
        }
        let Some(mut chain) = chain else {
            return;
        };
        chain.result = construction.result.clone();
        allocation.kind = SemanticStatementKind::Instruction(chain);
    }
}

impl SemanticFolder for StringBuildingRecovery {
    type Error = SemanticFoldError;

    fn finish_node(&mut self, mut node: SemanticNode) -> Result<SemanticNode, Self::Error> {
        if let SemanticNode::BasicBlock(block) = &mut node {
            self.changed |= self.merge(&mut block.statements);
        }
        Ok(node)
    }
}
