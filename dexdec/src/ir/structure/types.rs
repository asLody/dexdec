//! Type definitions for control flow structuring.

use std::fmt;

use crate::ir::{
    BlockId, EdgeKind, RegionId, RegionInvariantError, SemanticBuildError, SemanticFoldError,
    SemanticLabel,
};

use super::AcyclicStructureError;

/// Error during structuring.
#[derive(Debug)]
pub enum StructureError {
    UnknownRegion(RegionId),
    MissingEntry(RegionId),
    MissingBlock(BlockId),
    MissingReduction(RegionId),
    InvalidHandlerRegion {
        owner: RegionId,
        handler: RegionId,
    },
    MultipleFinallyRegions {
        owner: RegionId,
        first: RegionId,
        second: RegionId,
    },
    RegionEntryMissing {
        region: RegionId,
        entry: BlockId,
    },
    ConflictingEntryPort {
        owner: RegionId,
        entry: BlockId,
    },
    RegionOwnerMissing {
        region: RegionId,
        block: BlockId,
    },
    BoundaryIdExhausted(RegionId),
    GraphNodeIdExhausted(RegionId),
    MalformedFlowGraph(RegionId),
    MalformedFlowNode(BlockId),
    CyclicFlowGraph(RegionId),
    UnclassifiedSuccessors {
        region: RegionId,
        block: BlockId,
        count: usize,
    },
    MalformedBranch {
        region: RegionId,
        block: BlockId,
        edges: Vec<EdgeKind>,
    },
    SwitchMissingTerminator(BlockId),
    SwitchWrongTerminator(BlockId),
    SwitchMissingSelector(BlockId),
    SwitchMissingArms(BlockId),
    SwitchMissingArmLabels {
        header: BlockId,
        arm: BlockId,
    },
    MalformedSwitchEdge {
        header: BlockId,
        edge: EdgeKind,
    },
    Acyclic {
        region: RegionId,
        source: AcyclicStructureError,
    },
    Region(RegionInvariantError),
    Semantic(SemanticBuildError),
    SemanticFold(SemanticFoldError),
    ContinuationTargetMissing {
        scope: RegionId,
        target: BlockId,
    },
    MissingControlTarget(RegionId),
    ConflictingChildFlow(RegionId),
    UnboundContinuation {
        scope: RegionId,
        target: BlockId,
    },
    EscapedLoopLabel {
        region: RegionId,
        label: SemanticLabel,
    },
    EscapedGraphLabel {
        region: RegionId,
        node: BlockId,
        label: SemanticLabel,
    },
    EscapedChildLabel {
        owner: RegionId,
        child: RegionId,
        entry: BlockId,
        stage: &'static str,
        label: SemanticLabel,
    },
    EscapedRootLabel {
        stage: &'static str,
        label: SemanticLabel,
    },
    SemanticItemLimit {
        region: RegionId,
        stage: &'static str,
        items: usize,
        limit: usize,
    },
}

impl fmt::Display for StructureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownRegion(region) => write!(f, "unknown region {region}"),
            Self::MissingEntry(region) => write!(f, "region {region} has no entry"),
            Self::MissingBlock(block) => write!(f, "missing CFG block {block}"),
            Self::MissingReduction(region) => {
                write!(f, "region {region} has no reduced semantic node")
            }
            Self::InvalidHandlerRegion { owner, handler } => {
                write!(f, "region {handler} is not a handler child of {owner}")
            }
            Self::MultipleFinallyRegions {
                owner,
                first,
                second,
            } => write!(
                f,
                "region {owner} has multiple finally regions {first} and {second}"
            ),
            Self::RegionEntryMissing { region, entry } => {
                write!(
                    f,
                    "region CFG for {region} has no representative for entry {entry}"
                )
            }
            Self::ConflictingEntryPort { owner, entry } => {
                write!(f, "region {owner} exports conflicting entry {entry}")
            }
            Self::RegionOwnerMissing { region, block } => {
                write!(f, "region CFG for {region} has no owner for block {block}")
            }
            Self::BoundaryIdExhausted(region) => {
                write!(
                    f,
                    "region CFG for {region} exhausted synthetic block identifiers"
                )
            }
            Self::GraphNodeIdExhausted(region) => {
                write!(f, "semantic graph for {region} exhausted node identifiers")
            }
            Self::MalformedFlowGraph(region) => {
                write!(f, "semantic flow graph for {region} is malformed")
            }
            Self::MalformedFlowNode(block) => {
                write!(f, "semantic flow node {block} is malformed")
            }
            Self::CyclicFlowGraph(region) => {
                write!(
                    f,
                    "semantic flow graph for {region} remained cyclic after reduction"
                )
            }
            Self::UnclassifiedSuccessors {
                region,
                block,
                count,
            } => write!(
                f,
                "block {block} in {region} has {count} unclassified normal successors"
            ),
            Self::MalformedBranch {
                region,
                block,
                edges,
            } => write!(
                f,
                "conditional block {block} in {region} has malformed edges {edges:?}"
            ),
            Self::SwitchMissingTerminator(header) => {
                write!(f, "switch header {header} has no terminator")
            }
            Self::SwitchWrongTerminator(header) => {
                write!(f, "switch header {header} has a non-switch terminator")
            }
            Self::SwitchMissingSelector(header) => {
                write!(f, "switch header {header} has no selector")
            }
            Self::SwitchMissingArms(header) => {
                write!(f, "switch header {header} has no resolvable arms")
            }
            Self::SwitchMissingArmLabels { header, arm } => {
                write!(f, "switch {header} lost labels for arm {arm}")
            }
            Self::MalformedSwitchEdge { header, edge } => {
                write!(f, "switch {header} has non-dispatch edge {edge:?}")
            }
            Self::Acyclic { region, source } => {
                write!(f, "acyclic structuring for {region} failed: {source}")
            }
            Self::Region(source) => write!(f, "region fact query failed: {source}"),
            Self::Semantic(source) => write!(f, "semantic construction failed: {source}"),
            Self::SemanticFold(source) => {
                write!(f, "semantic continuation binding failed: {source}")
            }
            Self::ContinuationTargetMissing { scope, target } => {
                write!(
                    f,
                    "continuation in {scope} targets unavailable block {target}"
                )
            }
            Self::MissingControlTarget(region) => {
                write!(f, "control region {region} has no lexical transfer target")
            }
            Self::ConflictingChildFlow(region) => {
                write!(
                    f,
                    "region {region} has incompatible lexical and boundary flows"
                )
            }
            Self::UnboundContinuation { scope, target } => {
                write!(
                    f,
                    "root semantic graph retains continuation {scope} -> {target}"
                )
            }
            Self::EscapedLoopLabel { region, label } => {
                write!(
                    f,
                    "loop reduction in {region} left label {}:{} outside its lexical scope",
                    label.region, label.block
                )
            }
            Self::EscapedGraphLabel {
                region,
                node,
                label,
            } => {
                write!(
                    f,
                    "semantic flow node {node} in {region} moved label {}:{} outside its control domain",
                    label.region, label.block
                )
            }
            Self::EscapedChildLabel {
                owner,
                child,
                entry,
                stage,
                label,
            } => {
                write!(
                    f,
                    "{stage} child {child} at {entry} in {owner} moved loop label {}:{} outside its lexical scope",
                    label.region, label.block
                )
            }
            Self::EscapedRootLabel { stage, label } => {
                write!(
                    f,
                    "{stage} root reduction moved loop label {}:{} outside its lexical scope",
                    label.region, label.block
                )
            }
            Self::SemanticItemLimit {
                region,
                stage,
                items,
                limit,
            } => write!(
                f,
                "semantic structure for {region} has {items} nodes and operations after {stage}, above the {limit} item safety limit"
            ),
        }
    }
}

impl std::error::Error for StructureError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Acyclic { source, .. } => Some(source),
            Self::Region(source) => Some(source),
            Self::Semantic(source) => Some(source),
            Self::SemanticFold(source) => Some(source),
            _ => None,
        }
    }
}

impl From<RegionInvariantError> for StructureError {
    fn from(source: RegionInvariantError) -> Self {
        Self::Region(source)
    }
}

impl From<SemanticBuildError> for StructureError {
    fn from(source: SemanticBuildError) -> Self {
        Self::Semantic(source)
    }
}

impl From<SemanticFoldError> for StructureError {
    fn from(source: SemanticFoldError) -> Self {
        Self::SemanticFold(source)
    }
}
