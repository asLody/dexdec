//! Region-based structured control-flow IR.
//!
//! This module is the canonical ownership model for structuring. It mirrors the
//! key ILSpy invariant: local branches stay inside their container, and any
//! cross-container transfer is represented explicitly as a leave edge targeting
//! a structured region.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[path = "region/builder.rs"]
mod builder;
#[path = "region/control.rs"]
mod control;
#[path = "region/exceptions.rs"]
mod exceptions;
#[path = "region/exits.rs"]
mod exits;
#[path = "region/ownership.rs"]
mod ownership;
#[path = "region/synchronization.rs"]
mod synchronization;
#[path = "region/tree.rs"]
mod tree;
#[path = "region/verify.rs"]
mod verify;

use exits::CleanupChainAnalysis;
use ownership::LexicalOwnershipClosure;
use verify::RegionGraphVerifier;

pub use builder::RegionGraphBuilder;

use super::analysis::{ControlFlowFacts, DominanceError};
use super::{BlockId, EdgeKind, InsnArg, CFG};

/// Stable identifier for a structured control-flow region.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RegionId(u32);

impl RegionId {
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    pub const fn raw(self) -> u32 {
        self.0
    }
}

impl fmt::Display for RegionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "R{}", self.0)
    }
}

/// High-level owner for blocks and nested structured constructs.
#[derive(Debug, Clone)]
pub enum RegionKind {
    Method,
    Try,
    Catch(CatchRegion),
    Finally,
    Cleanup(CatchRegion),
    Synchronized(SynchronizedRegion),
    Loop(LoopRegion),
    Switch(SwitchRegion),
}

#[derive(Debug, Clone)]
pub struct CatchRegion {
    pub exception_types: Vec<super::ArgType>,
    pub exception_value: Option<super::RegisterArg>,
    /// Shared ordinary CFG continuation used when the handler entry cannot be
    /// owned lexically by this catch region.
    pub continuation: Option<BlockId>,
}

#[derive(Debug, Clone)]
pub struct SynchronizedRegion {
    pub lock: InsnArg,
    pub method: bool,
    /// Exception-handler regions proved to implement monitor release rather
    /// than source-level catch/finally semantics.
    pub release_handlers: BTreeSet<RegionId>,
}

#[derive(Debug, Clone)]
pub struct LoopRegion {
    pub follow: Option<BlockId>,
    pub latches: BTreeSet<BlockId>,
}

#[derive(Debug, Clone)]
pub struct SwitchRegion {
    pub follow: Option<BlockId>,
}

impl RegionKind {
    pub(crate) fn encloses_coincident(&self, inner: &Self) -> bool {
        match self {
            Self::Method => !matches!(inner, Self::Method),
            Self::Try | Self::Synchronized(_) => matches!(
                inner,
                Self::Catch(_) | Self::Finally | Self::Cleanup(_) | Self::Loop(_) | Self::Switch(_)
            ),
            Self::Catch(_) | Self::Finally | Self::Cleanup(_) => {
                matches!(inner, Self::Loop(_) | Self::Switch(_))
            }
            Self::Loop(_) => matches!(inner, Self::Switch(_)),
            Self::Switch(_) => false,
        }
    }

    pub fn is_finally_handler(&self) -> bool {
        matches!(self, RegionKind::Finally)
    }

    pub fn is_release_handler(&self) -> bool {
        matches!(self, RegionKind::Finally | RegionKind::Cleanup(_))
    }

    pub fn follow(&self) -> Option<BlockId> {
        match self {
            Self::Loop(region) => region.follow,
            Self::Switch(region) => region.follow,
            _ => None,
        }
    }

    pub fn continuation(&self) -> Option<BlockId> {
        match self {
            Self::Catch(handler) | Self::Cleanup(handler) => handler.continuation,
            _ => None,
        }
    }
}

/// Structured reason for leaving a region.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RegionExitKind {
    FallThrough,
    Return,
    Throw,
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub enum RegionExit {
    FallThrough(BlockId),
    Return(Option<InsnArg>),
    Throw(InsnArg),
    Break,
    Continue,
}

impl RegionExit {
    pub fn kind(&self) -> RegionExitKind {
        match self {
            Self::FallThrough(_) => RegionExitKind::FallThrough,
            Self::Return(_) => RegionExitKind::Return,
            Self::Throw(_) => RegionExitKind::Throw,
            Self::Break => RegionExitKind::Break,
            Self::Continue => RegionExitKind::Continue,
        }
    }

    pub fn value(&self) -> Option<&InsnArg> {
        match self {
            Self::Return(value) => value.as_ref(),
            Self::Throw(value) => Some(value),
            Self::FallThrough(_) | Self::Break | Self::Continue => None,
        }
    }

    pub fn continuation(&self) -> Option<BlockId> {
        match self {
            Self::FallThrough(target) => Some(*target),
            Self::Return(_) | Self::Throw(_) | Self::Break | Self::Continue => None,
        }
    }
}

/// Region-level interpretation of a CFG edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionTransferKind {
    /// The edge stays inside the same region.
    Local,
    /// The edge enters a child/nested region.
    Enter,
    /// The edge leaves the source region or jumps to a sibling region.
    Leave,
}

/// A CFG edge annotated with region ownership.
#[derive(Debug, Clone)]
pub struct RegionTransfer {
    pub source_block: BlockId,
    /// Physical target of the original CFG edge.
    pub target_block: BlockId,
    pub edge_kind: EdgeKind,
    pub source_region: RegionId,
    /// Owner of the physical CFG target.
    pub target_region: RegionId,
    /// Target after proven duplicated-cleanup contractions.
    pub destination_block: BlockId,
    pub destination_region: RegionId,
    pub leave_target: Option<RegionId>,
    pub kind: RegionTransferKind,
    pub exit_kind: RegionExitKind,
}

impl RegionTransfer {
    pub fn exit_destination(&self, method: RegionId) -> RegionId {
        match self.exit_kind {
            RegionExitKind::Return => method,
            _ => self.leave_target.unwrap_or(self.destination_region),
        }
    }

    pub fn requires_leave(&self, _cfg: &CFG) -> bool {
        match self.exit_kind {
            RegionExitKind::FallThrough => self.kind == RegionTransferKind::Leave,
            RegionExitKind::Return => true,
            RegionExitKind::Break => true,
            RegionExitKind::Continue => true,
            RegionExitKind::Throw => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegionEdge {
    pub source: BlockId,
    pub target: BlockId,
    pub kind: EdgeKind,
}

/// A first-class cross-region control transfer.
#[derive(Debug, Clone)]
pub struct RegionLeave {
    pub source: RegionId,
    pub target: RegionId,
    pub exit: RegionExit,
    pub source_block: Option<BlockId>,
    pub control_target: Option<RegionId>,
    pub edge: Option<RegionEdge>,
}

/// A leave resolved with the cleanup regions it must execute before reaching its target.
#[derive(Debug, Clone)]
pub struct ResolvedRegionExit {
    pub leave: RegionLeave,
    pub cleanup_regions: Vec<RegionId>,
}

impl RegionLeave {
    pub fn new(source: RegionId, target: RegionId, exit: RegionExit) -> Self {
        Self {
            source,
            target,
            exit,
            source_block: None,
            control_target: None,
            edge: None,
        }
    }

    pub fn with_source_block(mut self, block: BlockId) -> Self {
        self.source_block = Some(block);
        self
    }

    pub fn with_edge(mut self, edge: RegionEdge) -> Self {
        self.edge = Some(edge);
        self
    }

    pub fn kind(&self) -> RegionExitKind {
        self.exit.kind()
    }

    pub fn value(&self) -> Option<&InsnArg> {
        self.exit.value()
    }
}

/// A structured region and the low-level blocks it owns.
#[derive(Debug, Clone)]
pub struct StructuredRegion {
    pub id: RegionId,
    pub kind: RegionKind,
    pub parent: Option<RegionId>,
    pub entry: Option<BlockId>,
    pub blocks: BTreeSet<BlockId>,
    pub children: Vec<RegionId>,
}

struct LaminarPlacement {
    parent: RegionId,
    reparent: Vec<RegionId>,
}

enum RegionPlacement {
    Inserted(RegionId),
    Residual,
}

impl StructuredRegion {
    pub fn new(id: RegionId, kind: RegionKind, parent: Option<RegionId>) -> Self {
        Self {
            id,
            kind,
            parent,
            entry: None,
            blocks: BTreeSet::new(),
            children: Vec::new(),
        }
    }

    pub fn owns_block(&self, block: BlockId) -> bool {
        self.blocks.contains(&block)
    }
}

/// Region forest for one method. The root is always the method region.
#[derive(Debug, Clone)]
pub struct RegionTree {
    root: RegionId,
    next_id: u32,
    regions: BTreeMap<RegionId, StructuredRegion>,
}

/// Region ownership and resolved exits for one method.
#[derive(Debug, Clone)]
pub struct RegionGraph {
    tree: RegionTree,
    control_flow: ControlFlowFacts,
    exception_region_map: BTreeMap<u32, Vec<RegionId>>,
    exception_handlers: BTreeMap<RegionId, Vec<RegionId>>,
    handler_adapters: BTreeMap<BlockId, BlockId>,
    cleanup_representatives: BTreeMap<BlockId, BlockId>,
    cleanup_value_bindings: BTreeSet<(super::analysis::SsaVar, super::analysis::SsaVar)>,
    implicit_cleanup_completions: BTreeMap<RegionId, BTreeSet<BlockId>>,
    exceptional_contractions: Vec<(BlockId, BlockId)>,
    exceptional_rethrow_sources: BTreeMap<BlockId, BTreeSet<BlockId>>,
    block_owners: BTreeMap<BlockId, RegionId>,
    transfers: Vec<RegionTransfer>,
    leaves: Vec<ResolvedRegionExit>,
    edge_leaves: BTreeMap<RegionEdge, usize>,
    elisions: InstructionElisions,
}

#[derive(Debug, Clone, Default)]
struct InstructionElisions {
    candidates: BTreeSet<super::semantic::StatementOrigin>,
    source_equivalent: BTreeSet<super::semantic::StatementOrigin>,
}

impl InstructionElisions {
    fn from_candidates(candidates: BTreeSet<super::semantic::StatementOrigin>) -> Self {
        Self {
            candidates,
            source_equivalent: BTreeSet::new(),
        }
    }

    fn insert_source_equivalent(&mut self, origin: super::semantic::StatementOrigin) {
        self.candidates.insert(origin.clone());
        self.source_equivalent.insert(origin);
    }

    fn extend_source_equivalent(
        &mut self,
        origins: impl IntoIterator<Item = super::semantic::StatementOrigin>,
    ) {
        for origin in origins {
            self.insert_source_equivalent(origin);
        }
    }

    fn contains(&self, origin: &super::semantic::StatementOrigin) -> bool {
        self.candidates.contains(origin)
    }

    fn candidates(&self) -> &BTreeSet<super::semantic::StatementOrigin> {
        &self.candidates
    }

    fn is_source_equivalent(&self, origin: &super::semantic::StatementOrigin) -> bool {
        self.source_equivalent.contains(origin)
    }
}

impl RegionGraph {
    pub fn tree(&self) -> &RegionTree {
        &self.tree
    }

    pub fn control_continuation(&self, block: BlockId) -> BlockId {
        self.control_flow.structural_continuation(block)
    }

    pub(crate) fn semantic_dominates(&self, dominator: BlockId, block: BlockId) -> bool {
        self.control_flow
            .semantic_dominators()
            .dominates(dominator, block)
    }

    pub fn exception_regions(&self) -> &BTreeMap<u32, Vec<RegionId>> {
        &self.exception_region_map
    }

    pub fn handlers_of(&self, region: RegionId) -> &[RegionId] {
        self.exception_handlers
            .get(&region)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub fn is_exception_handler(&self, region: RegionId) -> bool {
        self.handler_owners(region).next().is_some()
    }

    pub fn is_synchronization_release_handler(&self, handler: RegionId) -> bool {
        self.tree.regions().any(|region| {
            matches!(
                &region.kind,
                RegionKind::Synchronized(synchronized)
                    if synchronized.release_handlers.contains(&handler)
            )
        })
    }

    /// Exception scopes that attach the given handler region.
    ///
    /// A handler may be physically placed below a wider lexical region while
    /// being semantically owned by a nested try.  Consumers that contract the
    /// region tree must use this relation instead of the tree parent.
    pub fn handler_owners(&self, handler: RegionId) -> impl Iterator<Item = RegionId> + '_ {
        self.exception_handlers
            .iter()
            .filter_map(move |(owner, handlers)| handlers.contains(&handler).then_some(*owner))
    }

    pub fn enclosing_exception_handler(&self, block: BlockId) -> Option<RegionId> {
        let owner = self.owner_of(block)?;
        self.tree
            .parent_chain(owner)
            .ok()?
            .into_iter()
            .find(|region| self.is_exception_handler(*region))
    }

    pub fn handler_adapters(&self) -> &BTreeMap<BlockId, BlockId> {
        &self.handler_adapters
    }

    pub fn cleanup_representative(&self, block: BlockId) -> Option<BlockId> {
        self.cleanup_representatives.get(&block).copied()
    }

    pub fn cleanup_representatives(&self) -> &BTreeMap<BlockId, BlockId> {
        &self.cleanup_representatives
    }

    pub fn cleanup_value_bindings(
        &self,
    ) -> &BTreeSet<(super::analysis::SsaVar, super::analysis::SsaVar)> {
        &self.cleanup_value_bindings
    }

    pub fn is_implicit_cleanup_completion(&self, region: RegionId, block: BlockId) -> bool {
        self.implicit_cleanup_completions
            .get(&region)
            .is_some_and(|completions| completions.contains(&block))
    }

    /// Whether a physical rethrow is the implicit completion of a source-level
    /// cleanup enclosing `region`.
    ///
    /// Cleanup recovery removes duplicated normal cleanup code and records the
    /// exceptional clone's rethrow as completion metadata. Nested control
    /// regions inside that clone must consume the same fact; otherwise the
    /// physical rethrow is emitted inside `finally` and makes its normal path
    /// appear terminal.
    pub fn is_enclosed_implicit_cleanup_completion(
        &self,
        region: RegionId,
        block: BlockId,
    ) -> Result<bool, RegionInvariantError> {
        for cleanup in self
            .implicit_cleanup_completions
            .iter()
            .filter_map(|(cleanup, completions)| completions.contains(&block).then_some(*cleanup))
        {
            if cleanup == region || self.tree.is_ancestor(cleanup, region)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub fn exceptional_contractions(&self) -> &[(BlockId, BlockId)] {
        &self.exceptional_contractions
    }

    pub fn exceptional_rethrow_sources(&self, block: BlockId) -> Option<&BTreeSet<BlockId>> {
        self.exceptional_rethrow_sources.get(&block)
    }

    pub fn transfers(&self) -> &[RegionTransfer] {
        &self.transfers
    }

    pub fn leaves(&self) -> &[ResolvedRegionExit] {
        &self.leaves
    }

    pub fn is_elided(&self, origin: &super::semantic::StatementOrigin) -> bool {
        self.elisions.contains(origin)
    }

    pub(crate) fn is_elided_in(
        &self,
        cfg: &CFG,
        region: RegionId,
        origin: &super::semantic::StatementOrigin,
    ) -> Result<bool, RegionInvariantError> {
        exits::OccurrenceElision::new(cfg, &self.tree, &self.exception_handlers, &self.elisions)
            .contains(region, origin)
    }

    pub fn leave_for_edge(&self, edge: RegionEdge) -> Option<&ResolvedRegionExit> {
        self.edge_leaves
            .get(&edge)
            .and_then(|index| self.leaves.get(*index))
    }

    pub fn owner_of(&self, block: BlockId) -> Option<RegionId> {
        self.block_owners.get(&block).copied()
    }

    pub fn cleanup_chain(
        &self,
        source: RegionId,
        target: RegionId,
    ) -> Result<Vec<RegionId>, RegionInvariantError> {
        CleanupChainAnalysis::new(&self.tree, &self.exception_handlers).between(source, target)
    }

    pub fn verify(&self, cfg: &CFG) -> Result<(), RegionInvariantError> {
        RegionGraphVerifier::new(self, cfg).verify()
    }
}

#[derive(Debug, Clone)]
pub enum RegionInvariantError {
    Dominance(DominanceError),
    MissingBlock(BlockId),
    MalformedSwitch {
        block: BlockId,
        successors: Vec<BlockId>,
    },
    MissingControlTarget {
        block: BlockId,
        kind: RegionExitKind,
    },
    InvalidLeaveKind {
        block: BlockId,
        kind: RegionExitKind,
    },
    MissingExitValue(BlockId),
    DuplicateExceptionRegion,
    ConflictingHandlerAdapter {
        block: BlockId,
        left: BlockId,
        right: BlockId,
    },
    ConflictingCleanupContraction {
        block: BlockId,
        left: BlockId,
        right: BlockId,
    },
    MissingExceptionRegion(u32),
    MissingExceptionParent {
        region: u32,
        parent: u32,
    },
    AmbiguousExceptionHandlerParent {
        region: u32,
        handlers: Vec<(u32, BlockId)>,
    },
    EmptyExceptionRegion(u32),
    ExceptionRegionCycle(Vec<u32>),
    MixedHandlerKinds {
        region: u32,
        entry: BlockId,
    },
    MixedExceptionRegisters {
        region: u32,
        entry: BlockId,
    },
    MissingSynchronizationHandler {
        region: RegionId,
        entry: BlockId,
    },
    InvalidSynchronizationRelease {
        region: RegionId,
        handler: RegionId,
    },
    ConflictingSynchronizationFacts {
        enter: super::semantic::StatementOrigin,
    },
    SynchronizationHandlerDomainMismatch {
        entry: BlockId,
        block: BlockId,
        expected: BTreeSet<RegionId>,
        actual: BTreeSet<RegionId>,
        closure: BTreeSet<BlockId>,
    },
    SynchronizationHandlerDomainOverlap {
        entry: BlockId,
        blocks: BTreeSet<BlockId>,
    },
    SynchronizationRegionOverlap {
        entry: BlockId,
        blocks: BTreeSet<BlockId>,
        regions: Vec<(RegionId, RegionKind, Option<BlockId>, BTreeSet<BlockId>)>,
    },
    UnknownRegion(RegionId),
    MissingRegionParent {
        region: RegionId,
        parent: RegionId,
    },
    MissingChildLink {
        parent: RegionId,
        child: RegionId,
    },
    ChildParentMismatch {
        parent: RegionId,
        child: RegionId,
        actual: Option<RegionId>,
    },
    RegionParentCycle(Vec<RegionId>),
    RegionEntryOutsideBody {
        region: RegionId,
        entry: BlockId,
    },
    AmbiguousOwner {
        block: BlockId,
        regions: Vec<RegionId>,
    },
    RegionOverlap {
        left: RegionId,
        right: RegionId,
        intersection: BTreeSet<BlockId>,
        left_only: BTreeSet<BlockId>,
        right_only: BTreeSet<BlockId>,
    },
    UnnestedOverlap {
        left: RegionId,
        right: RegionId,
        left_parent: Option<RegionId>,
        right_parent: Option<RegionId>,
        left_kind: RegionKind,
        right_kind: RegionKind,
        left_entry: Option<BlockId>,
        right_entry: Option<BlockId>,
        left_blocks: BTreeSet<BlockId>,
        right_blocks: BTreeSet<BlockId>,
    },
    NoCommonAncestor {
        left: RegionId,
        right: RegionId,
    },
    MissingOwner(BlockId),
    UnknownOwner {
        block: BlockId,
        owner: RegionId,
    },
    OwnerDoesNotContainBlock {
        block: BlockId,
        owner: RegionId,
    },
    InvalidElision(super::semantic::StatementOrigin),
    TransferSourceMismatch {
        block: BlockId,
        expected: RegionId,
        actual: RegionId,
    },
    TransferTargetMismatch {
        block: BlockId,
        expected: RegionId,
        actual: RegionId,
    },
    TransferKindMismatch {
        block: BlockId,
        expected: RegionTransferKind,
        actual: RegionTransferKind,
    },
    LeaveTargetMismatch {
        block: BlockId,
        expected: Option<RegionId>,
        actual: Option<RegionId>,
    },
    MissingLeave {
        source_block: BlockId,
        source: RegionId,
        target: RegionId,
        kind: RegionExitKind,
    },
    UnknownLeaveEdge(RegionEdge),
    DuplicateLeaveEdge(RegionEdge),
    InvalidLeaveEdge(RegionEdge),
    InvalidLeaveIndex,
    CleanupChainMismatch {
        source: RegionId,
        target: RegionId,
        expected: Vec<RegionId>,
        actual: Vec<RegionId>,
    },
    AmbiguousCleanup {
        region: RegionId,
        handlers: Vec<RegionId>,
    },
    UncontainedRegion {
        entry: BlockId,
        blocks: BTreeSet<BlockId>,
    },
}

impl fmt::Display for RegionInvariantError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Dominance(source) => write!(f, "dominance analysis failed: {source}"),
            Self::MissingBlock(block) => write!(f, "missing CFG block {block}"),
            Self::MalformedSwitch { block, successors } => write!(
                f,
                "switch block {block} has indistinguishable successors {successors:?}"
            ),
            Self::MissingControlTarget { block, kind } => {
                write!(f, "{kind:?} from {block} has no enclosing control target")
            }
            Self::InvalidLeaveKind { block, kind } => {
                write!(f, "{kind:?} from {block} is not a semantic region leave")
            }
            Self::MissingExitValue(block) => {
                write!(f, "throw in {block} has no exception value")
            }
            Self::DuplicateExceptionRegion => write!(f, "duplicate exception region id"),
            Self::ConflictingHandlerAdapter { block, left, right } => write!(
                f,
                "handler adapter {block} contracts into both {left} and {right}"
            ),
            Self::ConflictingCleanupContraction { block, left, right } => write!(
                f,
                "cleanup block {block} contracts into both {left} and {right}"
            ),
            Self::MissingExceptionRegion(region) => {
                write!(f, "exception region {region} is missing")
            }
            Self::MissingExceptionParent { region, parent } => {
                write!(f, "exception region {region} has missing parent {parent}")
            }
            Self::AmbiguousExceptionHandlerParent { region, handlers } => write!(
                f,
                "exception region {region} has ambiguous handler parents {handlers:?}"
            ),
            Self::EmptyExceptionRegion(region) => {
                write!(f, "exception region {region} owns no protected block")
            }
            Self::ExceptionRegionCycle(regions) => {
                write!(f, "exception region parent cycle: {regions:?}")
            }
            Self::MixedHandlerKinds { region, entry } => write!(
                f,
                "exception region {region} groups incompatible handlers at {entry}"
            ),
            Self::MixedExceptionRegisters { region, entry } => write!(
                f,
                "exception region {region} groups incompatible exception values at {entry}"
            ),
            Self::MissingSynchronizationHandler { region, entry } => write!(
                f,
                "synchronized region {region} has no release handler at {entry}"
            ),
            Self::InvalidSynchronizationRelease { region, handler } => write!(
                f,
                "synchronized region {region} references invalid release handler {handler}"
            ),
            Self::ConflictingSynchronizationFacts { enter } => write!(
                f,
                "monitor entry {}:{} has inconsistent synchronization proofs",
                enter.block, enter.instruction
            ),
            Self::SynchronizationHandlerDomainMismatch {
                entry,
                block,
                expected,
                actual,
                closure,
            } => write!(
                f,
                "synchronized handler domain at {entry} closes over {block} with handlers {actual:?}, expected {expected:?}: {closure:?}"
            ),
            Self::SynchronizationHandlerDomainOverlap { entry, blocks } => write!(
                f,
                "synchronized handler domain at {entry} cannot be nested: {blocks:?}"
            ),
            Self::SynchronizationRegionOverlap {
                entry,
                blocks,
                regions,
            } => write!(
                f,
                "synchronized region at {entry} overlaps existing lexical regions {regions:?}: {blocks:?}"
            ),
            Self::UnknownRegion(region) => write!(f, "unknown structured region {region}"),
            Self::MissingRegionParent { region, parent } => {
                write!(f, "region {region} has missing parent {parent}")
            }
            Self::MissingChildLink { parent, child } => {
                write!(f, "region {parent} does not link child {child}")
            }
            Self::ChildParentMismatch {
                parent,
                child,
                actual,
            } => write!(
                f,
                "region {parent} links child {child}, whose parent is {actual:?}"
            ),
            Self::RegionParentCycle(regions) => {
                write!(f, "structured region parent cycle: {regions:?}")
            }
            Self::RegionEntryOutsideBody { region, entry } => {
                write!(f, "entry {entry} is outside region {region}")
            }
            Self::AmbiguousOwner { block, regions } => {
                write!(
                    f,
                    "block {block} has ambiguous innermost owners {regions:?}"
                )
            }
            Self::RegionOverlap {
                left,
                right,
                intersection,
                left_only,
                right_only,
            } => write!(
                f,
                "regions {left} and {right} partially overlap: shared={intersection:?}, left-only={left_only:?}, right-only={right_only:?}"
            ),
            Self::UnnestedOverlap {
                left,
                right,
                left_parent,
                right_parent,
                left_kind,
                right_kind,
                left_entry,
                right_entry,
                left_blocks,
                right_blocks,
            } => write!(
                f,
                "overlapping regions {left} ({left_kind:?}, parent={left_parent:?}, entry={left_entry:?}, blocks={left_blocks:?}) and {right} ({right_kind:?}, parent={right_parent:?}, entry={right_entry:?}, blocks={right_blocks:?}) are not related by lexical nesting"
            ),
            Self::NoCommonAncestor { left, right } => {
                write!(f, "regions {left} and {right} have no common ancestor")
            }
            Self::MissingOwner(block) => write!(f, "block {block} has no region owner"),
            Self::UnknownOwner { block, owner } => {
                write!(f, "block {block} references unknown owner {owner}")
            }
            Self::OwnerDoesNotContainBlock { block, owner } => {
                write!(f, "owner {owner} does not contain block {block}")
            }
            Self::InvalidElision(origin) => write!(
                f,
                "elided instruction origin {}:{} does not exist",
                origin.block, origin.instruction
            ),
            Self::TransferSourceMismatch {
                block,
                expected,
                actual,
            } => write!(
                f,
                "transfer from {block} uses owner {actual}, expected {expected}"
            ),
            Self::TransferTargetMismatch {
                block,
                expected,
                actual,
            } => write!(
                f,
                "transfer to {block} uses owner {actual}, expected {expected}"
            ),
            Self::TransferKindMismatch {
                block,
                expected,
                actual,
            } => write!(
                f,
                "transfer from {block} is {actual:?}, expected {expected:?}"
            ),
            Self::LeaveTargetMismatch {
                block,
                expected,
                actual,
            } => write!(
                f,
                "leave from {block} targets {actual:?}, expected {expected:?}"
            ),
            Self::MissingLeave {
                source_block,
                source,
                target,
                kind,
            } => write!(
                f,
                "cross-region edge from {source_block} ({source}) to {target} lacks a {kind:?} leave"
            ),
            Self::UnknownLeaveEdge(edge) => {
                write!(f, "region leave references unknown edge {edge:?}")
            }
            Self::DuplicateLeaveEdge(edge) => {
                write!(f, "region edge {edge:?} has multiple semantic leaves")
            }
            Self::InvalidLeaveEdge(edge) => {
                write!(f, "region leave disagrees with edge semantics for {edge:?}")
            }
            Self::InvalidLeaveIndex => write!(f, "region leave edge index is inconsistent"),
            Self::CleanupChainMismatch {
                source,
                target,
                expected,
                actual,
            } => write!(
                f,
                "leave {source} -> {target} has cleanup chain {actual:?}, expected {expected:?}"
            ),
            Self::AmbiguousCleanup { region, handlers } => write!(
                f,
                "try region {region} has multiple cleanup handlers {handlers:?}"
            ),
            Self::UncontainedRegion { entry, blocks } => write!(
                f,
                "control region at {entry} is not contained by the method region: {blocks:?}"
            ),
        }
    }
}

impl From<DominanceError> for RegionInvariantError {
    fn from(source: DominanceError) -> Self {
        Self::Dominance(source)
    }
}

impl std::error::Error for RegionInvariantError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Dominance(source) => Some(source),
            _ => None,
        }
    }
}
