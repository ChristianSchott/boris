use boris_shared::{BindingId, ConflictKind, Def, DefId, Expr, UnaryOp};
use hir_def::{
    path::{GenericArg, GenericArgs, Path},
    type_ref::{LifetimeRef, TypeBound},
    FunctionId, HasModule, TupleFieldId, TupleId,
};
use hir_ty::{
    db::{HirDatabase, InternedClosure},
    mir::{
        BasicBlockId, BorrowKind, LocalId, MirBody, MirLowerError, Operand, Place, ProjectionElem,
        Rvalue, StatementKind, TerminatorKind,
    },
    ClosureId, Interner, TyExt, TyKind,
};
use itertools::Itertools;
use la_arena::{Arena, ArenaMap, Idx, RawIdx};
use ra_ap_hir::TypeRef;
use ra_ap_hir_def as hir_def;
use ra_ap_hir_ty as hir_ty;
use ra_ap_ide::CrateId;
use smallvec::{smallvec, SmallVec};
use tuple::Map;

use crate::{
    builder::{BindingUsageHint, ThirBodyBuilder},
    move_path::{MoveData, MovePathId, PlaceElem, PlaceInfo, ProjectionKind},
};

pub struct MirBodyWalker<'a> {
    crate_id: CrateId,
    thir_builder: &'a ThirBodyBuilder<'a>,
    mir_body: &'a MirBody,
    db: &'a dyn HirDatabase,

    locations: Arena<Location>,
    block_locations: ArenaMap<BasicBlockId, BasicBlockLocationMap>,
    param_locations: Vec<(LocalId, LocationId)>,

    move_data: MoveData<'a>,
    binding_locals: ArenaMap<BindingId, LocalId>,
    local_bindings: ArenaMap<LocalId, BindingId>,
    local_captures: ArenaMap<LocalId, DefId>,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub struct Location(Option<DefId>);

pub type LocationId = Idx<Location>;
pub struct BasicBlockLocationMap {
    statements: Box<[LocationId]>,
    terminator: Option<LocationId>,
}

impl BasicBlockLocationMap {
    fn iter(&self) -> impl Iterator<Item = LocationId> + '_ {
        self.statements
            .iter()
            .cloned()
            .chain(self.terminator.iter().cloned())
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NodeKind {
    Value,
    Place(Option<BindingId>, bool), //  is root path?
    Deref {
        mutable: bool,
        binding: Option<BindingId>,
        lvalue: bool,
    },
    Drop,
}

#[derive(Debug, Clone)]
pub struct Node {
    pub kind: NodeKind,
    pub lifetimes: SmallVec<[LifetimeId; 1]>,
    pub span: Option<DefId>,
}
pub type NodeId = Idx<Node>;

#[derive(Debug, Clone)]
pub struct Conflict {
    pub kind: ConflictKind,
    pub from: NodeId,
    pub targets: Vec<NodeId>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EdgeKind {
    Ref { mutability: bool },
    Move,
    Copy,
    Deref,
    Reassign, // reassignment of mutable binding
    EndScope,
    Projection(ProjectionKind),
}

#[derive(Debug, Clone)]
pub struct Edge {
    pub to: NodeId,
    pub kind: EdgeKind,
}

#[derive(Debug, Clone, Default)]
pub struct Lifetime;
pub type LifetimeId = Idx<Lifetime>;

#[derive(Default, Debug, Clone)]
pub struct Graph {
    pub nodes: Arena<Node>,
    pub edges: ArenaMap<NodeId, Vec<Edge>>,

    pub lifetime: Arena<Lifetime>,
    pub constraints: ArenaMap<LifetimeId, Vec<LifetimeId>>,
    pub lifetime_nodes: ArenaMap<LifetimeId, Vec<NodeId>>,

    pub conflicts: Vec<Conflict>,
}

impl Graph {
    pub fn span(&self, id: NodeId) -> Option<DefId> {
        self.nodes[id].span
    }

    fn alloc(&mut self, kind: NodeKind, span: Option<DefId>) -> NodeId {
        self.nodes.alloc(Node {
            span,
            kind,
            lifetimes: smallvec![],
        })
    }

    fn alloc_rvalue(&mut self, span: Option<DefId>) -> NodeId {
        self.alloc(NodeKind::Value, span)
    }

    fn alloc_path(
        &mut self,
        move_data: &MoveData,
        move_path: MovePathId,
        binding: Option<BindingId>,
        span: Option<DefId>,
    ) -> SmallVec<[(MovePathId, NodeId); 1]> {
        let child_paths = move_data.children(move_path);
        if child_paths.is_empty() {
            let node = self.alloc(NodeKind::Place(binding, move_data.is_root(move_path)), span);
            self.create_lifetime_for_node(node, move_path, move_data);
            smallvec![(move_path, node)]
        } else {
            let node = self.alloc(NodeKind::Place(binding, move_data.is_root(move_path)), span);
            self.create_lifetime_for_node(node, move_path, move_data);
            let mut nodes = smallvec![(move_path, node)];
            for child_nodes in child_paths.iter().map(|(proj_kind, child_path)| {
                let child_nodes = self.alloc_path(move_data, *child_path, binding, span);
                if let Some((_, child_root)) = child_nodes.first() {
                    self.connect(node, *child_root, EdgeKind::Projection(*proj_kind));
                    self.connect_lifetimes(*child_root, node);
                }
                child_nodes
            }) {
                nodes.extend(child_nodes);
            }
            nodes
        }
    }

    fn associate_lt(&mut self, lt: LifetimeId, node: NodeId) {
        if !self.nodes[node].lifetimes.contains(&lt) {
            self.nodes[node].lifetimes.push(lt);
        }
        self.lifetime_nodes.entry(lt).or_default().push(node);
    }

    fn create_lifetime_for_node(
        &mut self,
        node: NodeId,
        move_path_id: MovePathId,
        move_data: &MoveData,
    ) -> Option<LifetimeId> {
        if move_data[move_path_id].contains_lt() {
            let lt = self.lifetime.alloc(Lifetime::default());
            self.associate_lt(lt, node);
            Some(lt)
        } else {
            None
        }
    }

    pub fn find_connected(&self, from: NodeId, kind: EdgeKind) -> Option<NodeId> {
        self.edges.get(from).and_then(|edges| {
            edges
                .iter()
                .find_map(|edge| (edge.kind == kind).then_some(edge.to))
        })
    }

    fn connect(&mut self, from: NodeId, to: NodeId, kind: EdgeKind) {
        self.edges.entry(from).or_default().push(Edge { to, kind });
    }

    fn connect_lifetimes(&mut self, from: NodeId, to: NodeId) {
        let (from_lts, to_lts) = (from, to).map(|id| self.nodes[id].lifetimes.clone());
        for (from, to) in from_lts.into_iter().cartesian_product(to_lts.into_iter()) {
            self.connect_lifetime(from, to);
        }
    }

    fn connect_lifetime(&mut self, a: LifetimeId, b: LifetimeId) {
        self.constraints.entry(a).or_default().push(b);
    }

    pub fn add_conflict(&mut self, conflict: Conflict) {
        self.conflicts.push(conflict);
    }
}

impl std::ops::Index<NodeId> for Graph {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self.nodes[index]
    }
}

#[derive(Debug, Clone, Default)]
pub struct NodeIds(SmallVec<[NodeId; 1]>);

impl NodeIds {
    fn merge(&mut self, other: &Self) {
        for other_source in other.0.iter() {
            if !self.0.contains(other_source) {
                self.0.push(*other_source);
            }
        }
    }

    fn iter(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.0.iter().cloned()
    }
}

impl From<NodeId> for NodeIds {
    fn from(value: NodeId) -> Self {
        Self(smallvec![value])
    }
}

impl PartialEq for NodeIds {
    fn eq(&self, other: &Self) -> bool {
        // contain same elements ignoring order
        self.0.len() == other.0.len() && self.0.iter().all(|x| other.0.contains(x))
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
struct MovePathState {
    source: NodeIds,
    moved: Option<NodeIds>,
    maybe_uninit: bool, // when the move path is initialized in one predecessor, but not the other one
}

impl MovePathState {
    fn assign(node: NodeId) -> MovePathState {
        MovePathState {
            source: node.into(),
            moved: None,
            maybe_uninit: false,
        }
    }

    fn merge(&mut self, other: &Self) {
        self.source.merge(&other.source);
        match (&mut self.moved, &other.moved) {
            (Some(moved), Some(other_moved)) => moved.merge(other_moved),
            (None, Some(other_moved)) => self.moved = Some(other_moved.clone()),
            _ => (),
        }
        self.maybe_uninit |= other.maybe_uninit;
    }

    fn set_maybe_uninit(&mut self) {
        if !self.source.0.is_empty() {
            self.maybe_uninit = true;
        }
    }

    fn mark_moved(&mut self, node: NodeId) {
        self.moved
            .get_or_insert_with(|| NodeIds::default())
            .0
            .push(node);
    }

    fn reset(&mut self) {
        self.source.0.clear();
        self.moved = None;
    }

    fn iter_sources(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.source.0.iter().cloned()
    }

    fn is_assigned(&self) -> bool {
        return !self.source.0.is_empty();
    }
}

#[derive(Debug, Default, Clone, PartialEq)]
struct MovePathStates(ArenaMap<MovePathId, MovePathState>);

impl MovePathStates {
    fn get(&self, move_path_id: MovePathId) -> Option<MovePathState> {
        self.0.get(move_path_id).cloned() // FIXME: why clone here?
    }

    fn merge(&mut self, other: &MovePathStates, move_data: &MoveData) {
        for (id, _) in move_data.move_paths.iter() {
            match (self.0.get_mut(id), other.0.get(id)) {
                (Some(state), Some(other_state)) => {
                    state.merge(other_state);
                }
                (None, Some(other_state)) => {
                    let mut new_state = other_state.clone();
                    new_state.set_maybe_uninit();
                    self.0.insert(id, new_state);
                }
                (Some(state), None) => {
                    state.set_maybe_uninit();
                }
                (None, None) => (),
            }
        }
    }

    fn apply_statement(&mut self, statement: &NodeStatement, move_data: &MoveData) {
        match statement {
            NodeStatement::Assignment { assigned, used } => {
                for (move_path, kind, node) in used.iter() {
                    if matches!(kind, EdgeKind::Move) {
                        move_data.for_each_child_path(*move_path, |child| {
                            if let Some(path_state) = self.0.get_mut(child) {
                                path_state.mark_moved(*node);
                            }
                        });
                    }
                }
                for (assigned_path, node) in assigned {
                    // self.0
                    //     .entry(*assigned_path)
                    //     .or_default()
                    //     .source
                    //     .merge(&ValueSources(smallvec![*node]));

                    self.0.insert(*assigned_path, MovePathState::assign(*node));
                }
            }
            NodeStatement::EndScope { move_path, .. } => {
                move_data.for_each_child_path(*move_path, |path| {
                    if let Some(state) = self.0.get_mut(path) {
                        state.reset();
                    }
                });
            }
        }
    }
}

enum NodeStatement {
    Assignment {
        assigned: SmallVec<[(MovePathId, NodeId); 1]>,
        used: SmallVec<[(MovePathId, EdgeKind, NodeId); 1]>,
    },
    EndScope {
        move_path: MovePathId,
        node: NodeId,
    },
}

pub fn walk_thir_body<'a>(
    thir_builder: &'a ThirBodyBuilder<'a>,
    db: &'a dyn HirDatabase,
    owner: FunctionId,
) -> Result<Graph, MirLowerError> {
    let mut graph = Graph::default();

    //  TODO: prop errors..
    let body = db.mir_body(owner.into())?; // FIXME: unwrap
    let body_walker = MirBodyWalker::new(thir_builder, &body, db);
    body_walker.walk(&mut graph, None, Some(thir_builder.return_binding()))?;
    Result::Ok(graph)
}

impl<'a> MirBodyWalker<'a> {
    pub fn new(
        thir_builder: &'a ThirBodyBuilder<'a>,
        mir_body: &'a MirBody,
        db: &'a dyn HirDatabase,
    ) -> MirBodyWalker<'a> {
        let module_id = mir_body.owner.module(db.upcast());
        let crate_id = module_id.krate();

        let binding_locals = mir_body
            .binding_locals
            .iter()
            .map(|(binding, local)| (thir_builder.map_binding(binding), *local))
            .collect::<ArenaMap<BindingId, LocalId>>();
        let local_bindings = binding_locals
            .iter()
            .map(|(binding, local)| (*local, binding))
            .collect::<ArenaMap<LocalId, BindingId>>();

        let mut locations = Arena::new();
        let block_locations: ArenaMap<BasicBlockId, BasicBlockLocationMap> = mir_body
            .basic_blocks
            .iter()
            .map(|(bb_id, bb)| {
                let loc_map = BasicBlockLocationMap {
                    statements: Box::from_iter(bb.statements.iter().map(|statement| {
                        locations.alloc(Location(thir_builder.map_to_def(statement.span)))
                    })),
                    terminator: bb
                        .terminator
                        .as_ref()
                        .map(|term| locations.alloc(Location(thir_builder.map_to_def(term.span)))),
                };
                (bb_id, loc_map)
            })
            .collect();
        let param_locations = mir_body
            .param_locals
            .iter()
            .map(|param| {
                let def = local_bindings
                    .get(*param)
                    .and_then(|binding| thir_builder.binding_def(*binding));
                (*param, locations.alloc(Location(def)))
            })
            .collect();

        // this is a bit of a workaround, to link locals captured by a closure to the proper DefId
        let mut local_captures: ArenaMap<LocalId, DefId> = ArenaMap::new();
        for (block_id, block) in mir_body.basic_blocks.iter() {
            for (stmnt, loc) in block
                .statements
                .iter()
                .zip_eq(block_locations[block_id].statements.iter().copied())
            {
                match (&stmnt.kind, locations[loc].0) {
                    (
                        StatementKind::Assign(
                            _,
                            Rvalue::Aggregate(hir_ty::mir::AggregateKind::Closure(_), ops),
                        ),
                        Some(closure_def),
                    ) => {
                        if !matches!(thir_builder[closure_def], Def::Expr(Expr::Closure { .. })) {
                            println!("Closure capture does not originate from closure def!?");
                        }
                        for op in ops.iter() {
                            match op {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    local_captures.insert(place.local, closure_def);
                                }
                                _ => (),
                            }
                        }
                    }
                    _ => (),
                }
            }
        }

        let move_data = MoveData::new(mir_body, db);
        MirBodyWalker {
            thir_builder,
            mir_body,
            db,
            move_data,
            locations,
            block_locations,
            param_locations,
            binding_locals,
            local_bindings,
            local_captures,
            crate_id,
        }
    }

    fn binding(&self, local: LocalId) -> Option<BindingId> {
        self.local_bindings.get(local).copied()
    }

    fn path_binding(&self, path: MovePathId) -> Option<BindingId> {
        self.binding(self.move_data.local(path))
    }

    // FIXME: naming.. this generates the graph, and does not 'walk' it
    pub fn walk(
        &self,
        graph: &mut Graph,
        captures: Option<&[(MovePathId, NodeId)]>,
        ret_def: Option<BindingId>,
    ) -> Result<(), MirLowerError> {
        let statements = self.graph_statements(graph, captures, ret_def)?;

        let block_sequence = self.basic_block_sequence();
        let block_sequence_inv = self.basic_block_sequence_inv(&block_sequence);

        let mut on_entry: ArenaMap<_, _> = self
            .iter_basic_block_ids()
            .map(|id| (id, MovePathStates::default()))
            .collect();
        let mut on_exit = on_entry.clone();

        // set parameter locals as initialized on entry of the first block
        let mut param_states = MovePathStates::default();
        self.param_locations
            .iter()
            .filter_map(|(_, loc)| statements.get(*loc))
            .for_each(|statement| param_states.apply_statement(statement, &self.move_data));
        on_entry.insert(self.mir_body.start_block, param_states.clone());

        let mut queue = self.iter_basic_block_ids().rev().collect_vec();
        // fix-point iteration
        while let Some(top) = queue.pop() {
            let mut move_path_states = on_entry[top].clone();
            // update move_path states
            for statement in self.block_locations[top]
                .iter()
                .filter_map(|loc| statements.get(loc))
            {
                move_path_states.apply_statement(statement, &self.move_data);
            }
            on_exit.insert(top, move_path_states);

            for target in block_sequence[top].iter().cloned() {
                // merge move path states of previous blocks
                let mut state = (target == self.mir_body.start_block)
                    .then(|| param_states.clone()) // not sure if this can actually occur, but better be safe. the start block should only be visited once at the beginning and never again..
                    .unwrap_or_default();
                block_sequence_inv[target]
                    .iter()
                    .filter_map(|prev_block| on_exit.get(*prev_block))
                    .for_each(|prev_state| state.merge(prev_state, &self.move_data));
                if on_entry
                    .get(target)
                    .map(|old_state| *old_state != state)
                    .unwrap_or(true)
                {
                    on_entry.insert(target, state);
                    if !queue.contains(&target) {
                        queue.push(target);
                    }
                }
            }
        }

        self.dependencies(graph, &on_entry, &statements);
        Result::Ok(())
    }

    const RETURN_LOCAL: LocalId = LocalId::from_raw(RawIdx::from_u32(0));
    const CAPTURE_LOCAL: LocalId = LocalId::from_raw(RawIdx::from_u32(1));

    fn graph_statements(
        &self,
        graph: &mut Graph,
        captures: Option<&[(MovePathId, NodeId)]>,
        ret_binding: Option<BindingId>,
    ) -> Result<ArenaMap<LocationId, NodeStatement>, MirLowerError> {
        enum PlaceProjection {
            Deref(NodeId, bool),
            MovePath(MovePathId),
        }
        type Usages = Vec<(MovePathId, EdgeKind, NodeId)>;

        let mut statements: ArenaMap<LocationId, NodeStatement> = ArenaMap::new();

        let project_place = |graph: &mut Graph,
                             span: Option<DefId>,
                             place: &Place,
                             usages: &mut Usages,
                             as_lvalue: Option<BindingId>|
         -> PlaceProjection {
            let projections = place.projection.lookup(&self.mir_body.projection_store);
            // check for index projections
            usages.extend(projections.iter().filter_map(|proj| match proj {
                PlaceElem::Index(local_id) => {
                    Some((
                        self.move_data.move_path_for(*local_id),
                        EdgeKind::Copy,
                        graph.alloc_rvalue(
                            span.and_then(|path| self.find_index_usage(path, *local_id)),
                        ),
                    ))
                }
                _ => None,
            }));

            let mut move_path = self.move_data.move_path_for(place.local);

            for proj in projections.iter() {
                if matches!(proj, PlaceElem::Deref) {
                    let PlaceInfo {
                        is_copy,
                        behind_mutable_ref,
                    } = self.move_data.place_info(place);
                    let behind_mutable_ref = behind_mutable_ref.expect("This place contains a deref, thus information about the reference should be present.");
                    let deref_node = graph.alloc(
                        match as_lvalue {
                            Some(binding) => NodeKind::Deref {
                                mutable: behind_mutable_ref,
                                binding: Some(binding),
                                lvalue: true,
                            },
                            None => NodeKind::Deref {
                                mutable: behind_mutable_ref,
                                binding: None,
                                lvalue: false,
                            },
                        },
                        span,
                    );
                    let lt = graph.lifetime.alloc(Lifetime::default());
                    graph.associate_lt(lt, deref_node);
                    usages.push((move_path, EdgeKind::Deref, deref_node));
                    return PlaceProjection::Deref(deref_node, is_copy);
                } else {
                    move_path = self.move_data.find_child(move_path, proj).unwrap();
                }
            }
            PlaceProjection::MovePath(move_path)
        };

        let place_to_lvalue =
            |graph: &mut Graph, place: &Place, location: LocationId, usages: &mut Usages| {
                let binding = self.place_binding(place).or_else(|| {
                    if place.local == Self::RETURN_LOCAL {
                        ret_binding
                    } else {
                        None
                    }
                });
                let span = binding
                    .and_then(|id| self.find_assignment(location, id))
                    .map(|id| self.find_path(id));
                match project_place(graph, span, place, usages, binding) {
                    PlaceProjection::Deref(node, _) => (node, smallvec![]),
                    PlaceProjection::MovePath(move_path) => {
                        let nodes = graph.alloc_path(&self.move_data, move_path, binding, span);
                        (nodes.first().unwrap().1, nodes)
                    }
                }
            };

        let use_place = |graph: &mut Graph,
                         place: &Place,
                         kind: EdgeKind,
                         span: Option<DefId>,
                         usages: &mut Usages| {
            match project_place(graph, span, place, usages, None) {
                PlaceProjection::Deref(node, is_copy) => {
                    if matches!(kind, EdgeKind::Move) && !is_copy {
                        graph.add_conflict(Conflict {
                            kind: ConflictKind::MoveOutOfRef,
                            from: node,
                            targets: vec![],
                        });
                    }
                    node
                }
                PlaceProjection::MovePath(path) => {
                    let node = graph.alloc_rvalue(span);
                    graph.create_lifetime_for_node(node, path, &self.move_data);
                    usages.push((path, kind, node));
                    node
                }
            }
        };

        let use_operand =
            |graph: &mut Graph, op: &Operand, loc: LocationId, index: u32, usages: &mut Usages| {
                match op {
                    Operand::Copy(place) | Operand::Move(place) => {
                        let span = self
                            .find_op_usage(loc, place, BindingUsageHint::Arg(index))
                            .map(|id| self.find_path(id));
                        Some(match project_place(graph, span, place, usages, None) {
                            PlaceProjection::Deref(node, is_copy) => {
                                if !is_copy {
                                    graph.add_conflict(Conflict {
                                        kind: ConflictKind::MoveOutOfRef,
                                        from: node,
                                        targets: vec![],
                                    });
                                }
                                node
                            }
                            PlaceProjection::MovePath(path) => {
                                let node = graph.alloc_rvalue(span);
                                graph.create_lifetime_for_node(node, path, &self.move_data);
                                let kind = self.move_data[path]
                                    .is_copy
                                    .then_some(EdgeKind::Copy)
                                    .unwrap_or(EdgeKind::Move);
                                usages.push((path, kind, node));
                                node
                            }
                        })
                    }
                    _ => None,
                }
            };

        let closure_def = |graph: &mut Graph,
                           loc: LocationId,
                           closure: ClosureId,
                           ops: &[Operand],
                           lvalue_node: NodeId,
                           usages: &mut Usages|
         -> Result<(), MirLowerError> {
            let span = self.location_def(loc);
            let capture_nodes = Box::from_iter(ops.iter().filter_map(|op| {
                Some(match op {
                    Operand::Copy(place) => use_place(graph, place, EdgeKind::Copy, span, usages),
                    Operand::Move(place) => use_place(graph, place, EdgeKind::Move, span, usages),
                    Operand::Constant(_) | Operand::Static(_) => {
                        println!("Invalid closure capture.");
                        return None;
                    }
                })
            }));
            for node in capture_nodes.iter() {
                graph.connect_lifetimes(*node, lvalue_node);
            }

            let closure_body = self.db.mir_body_for_closure(closure)?;
            let walker = MirBodyWalker::new(self.thir_builder, &closure_body, self.db);

            let (capture_binding, capture_def, ret_binding) = span
                .and_then(|id| match self.thir_builder[id] {
                    Def::Expr(Expr::Closure {
                        capture_binding,
                        capture_dummy,
                        return_binding,
                        ..
                    }) => Some((capture_binding, capture_dummy, return_binding)),
                    _ => None,
                })
                .map(|(a, b, c)| (Some(a), Some(b), Some(c)))
                .unwrap_or((None, None, None));
            let capture_path = walker.move_data.move_path_for(Self::CAPTURE_LOCAL);
            let root_node = graph.alloc(NodeKind::Place(capture_binding, true), capture_def);
            graph.create_lifetime_for_node(root_node, capture_path, &walker.move_data);

            let mut capture_assignments = vec![(capture_path, root_node)];
            for (proj, child_path) in walker.move_data.children(capture_path) {
                match proj {
                    ProjectionKind::Deref => {
                        // FIXME: without proper lt-support, we can not distinguish the lts of different closure captures, when capturing by ref
                        break;
                    }
                    ProjectionKind::ClosureField(index) => {
                        let binding = ops.get(*index).and_then(|op| match op {
                            Operand::Copy(p) | Operand::Move(p) => self.binding(p.local),
                            _ => None,
                        });
                        capture_assignments.extend_from_slice(&graph.alloc_path(
                            &walker.move_data,
                            *child_path,
                            binding,
                            capture_def,
                        ));
                    }
                    _ => println!("Non closure field projection in closure!"),
                }
            }
            graph.connect_lifetimes(lvalue_node, root_node);

            walker.walk(graph, Some(&capture_assignments), ret_binding)
        };

        for (block_id, block) in self.mir_body.basic_blocks.iter() {
            for (stmnt, loc) in block
                .statements
                .iter()
                .zip_eq(self.block_locations[block_id].statements.iter().copied())
            {
                match &stmnt.kind {
                    StatementKind::Assign(lvalue, value) => {
                        let mut usages = vec![];
                        let (lvalue_node, assigned) =
                            place_to_lvalue(graph, lvalue, loc, &mut usages);
                        match value {
                            Rvalue::Use(op)
                            | Rvalue::Repeat(op, _)
                            | Rvalue::UnaryOp(_, op)
                            | Rvalue::ShallowInitBox(op, _)
                            | Rvalue::Cast(_, op, _) => {
                                if let Some(rvalue_node) =
                                    use_operand(graph, op, loc, 0, &mut usages)
                                {
                                    graph.connect_lifetimes(rvalue_node, lvalue_node);
                                }
                            }
                            Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                                use_operand(graph, lhs, loc, 0, &mut usages);
                                use_operand(graph, rhs, loc, 1, &mut usages);
                            }
                            Rvalue::Aggregate(kind, ops) => match kind {
                                hir_ty::mir::AggregateKind::Adt(_, _)
                                | hir_ty::mir::AggregateKind::Array(_)
                                | hir_ty::mir::AggregateKind::Union(_, _) => {
                                    let op_nodes = ops
                                        .iter()
                                        .enumerate()
                                        .filter_map(|(index, op)| {
                                            use_operand(graph, op, loc, index as u32, &mut usages)
                                        })
                                        .collect_vec();
                                    for op_node in op_nodes {
                                        graph.connect_lifetimes(op_node, lvalue_node);
                                    }
                                }
                                hir_ty::mir::AggregateKind::Tuple(ty) => {
                                    match ty.kind(Interner) {
                                        TyKind::Tuple(_, _) => {
                                            for (index, op) in ops.iter().enumerate() {
                                                if let Some((op_node, lvalue_node)) = use_operand(
                                                    graph,
                                                    op,
                                                    loc,
                                                    index as u32,
                                                    &mut usages,
                                                )
                                                .zip(graph.find_connected(
                                                    lvalue_node,
                                                    EdgeKind::Projection(ProjectionKind::Field(
                                                        either::Either::Right(TupleFieldId {
                                                            tuple: TupleId(!0), // this is currently just a dummy and unused by mir lowering
                                                            index: index as u32,
                                                        }),
                                                    )),
                                                )) {
                                                    graph.connect_lifetimes(op_node, lvalue_node);
                                                }
                                            }
                                        }
                                        _ => panic!("not a tuple."),
                                    }
                                }
                                hir_ty::mir::AggregateKind::Closure(ty) => {
                                    match ty.kind(Interner) {
                                        TyKind::Closure(id, _) => {
                                            closure_def(
                                                graph,
                                                loc,
                                                *id,
                                                &ops,
                                                lvalue_node,
                                                &mut usages,
                                            )?;
                                        }
                                        _ => panic!("not a closure."),
                                    }
                                }
                            },
                            Rvalue::Ref(kind, place) => {
                                let span = if let Some(closure_def) =
                                    self.local_captures.get(lvalue.local)
                                {
                                    Some(*closure_def) // if the assigned place, is captured by a closure afterwards, we use the DefId of the closure
                                } else {
                                    self.find_op_usage(loc, place, BindingUsageHint::None)
                                };

                                let kind = EdgeKind::Ref {
                                    mutability: match kind {
                                        BorrowKind::Shared | BorrowKind::Shallow => false,
                                        BorrowKind::Mut { .. } => true,
                                    },
                                };

                                let ref_node = use_place(graph, place, kind, span, &mut usages);
                                if graph[ref_node].lifetimes.is_empty() {
                                    let lt = graph.lifetime.alloc(Lifetime::default());
                                    graph.associate_lt(lt, ref_node);
                                }

                                graph.connect_lifetimes(ref_node, lvalue_node);
                            }
                            Rvalue::CopyForDeref(place) => {
                                let kind = EdgeKind::Copy; // is this correct?
                                let span = self.find_usage(loc, place);
                                let node = use_place(graph, place, kind, span, &mut usages);
                                graph.connect_lifetimes(node, lvalue_node);
                            }
                            Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                                let kind = EdgeKind::Copy; // is this correct?
                                let span = self.find_usage(loc, place);
                                use_place(graph, place, kind, span, &mut usages);
                            }
                            _ => (),
                        };

                        statements.insert(
                            loc,
                            NodeStatement::Assignment {
                                assigned,
                                used: usages.into(),
                            },
                        );
                    }
                    StatementKind::StorageDead(local) => {
                        if self.binding(*local).is_some() {
                            let move_path = self.move_data.move_path_for(*local);
                            let def = self
                                .location_def(loc)
                                .map(|def| self.thir_builder.find_drop_def(def));
                            let node = graph.alloc(NodeKind::Drop, def);
                            statements.insert(loc, NodeStatement::EndScope { move_path, node });
                        }
                    }
                    _ => (),
                }
            }
            if let Some((term, loc)) = block
                .terminator
                .as_ref()
                .zip(self.block_locations[block_id].terminator)
            {
                let mut usages = vec![];
                let statement = match &term.kind {
                    TerminatorKind::Call {
                        destination,
                        func,
                        args,
                        ..
                    } => {
                        let (lvalue_node, assigned) =
                            place_to_lvalue(graph, destination, loc, &mut usages);
                        // func is just a constant anyway
                        // use_operand(graph, func, loc, 0, &mut usages);

                        match func {
                            Operand::Constant(c) => match c.data(Interner).ty.kind(Interner) {
                                TyKind::FnDef(def_id, _) => {
                                    // check which lts have a dependency to the return type..
                                    // manually do lt-elision: https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html#lifetime-elision

                                    let callable_def =
                                        self.db.lookup_intern_callable_def((*def_id).into());

                                    match callable_def {
                                        hir_ty::CallableDefId::FunctionId(func) => {
                                            let fn_data = self.db.function_data(func);
                                            // FIXME: for closure call, first arg is the closure and the second one is the arguments,
                                            // but if the closure arguments are empty, args.len() == 0
                                            // assert_eq!(args.len(), fn_data.params.len());

                                            if let Some(ret_lts) = (!graph[lvalue_node]
                                                .lifetimes
                                                .is_empty())
                                            .then(|| {
                                                self.find_lifetimes_in_type_ref(&fn_data.ret_type)
                                            })
                                            .and_then(|ret_lts| {
                                                (!ret_lts.is_empty()).then_some(ret_lts)
                                            }) {
                                                let args = Box::from_iter(args
                                                    .iter()
                                                    .enumerate()
                                                    .zip(fn_data.params.iter()).filter_map(|((i, arg), param)| {
                                                        use_operand(
                                                            graph,
                                                            arg,
                                                            loc,
                                                            i as u32,
                                                            &mut usages,
                                                        ).map(|node| (node, self.find_lifetimes_in_type_ref(&param)))
                                                    }));

                                                for ret_lt in ret_lts.iter() {
                                                    let mut matched = false;
                                                    for (arg_node, lts) in args.iter() {
                                                        if lts.contains(ret_lt) {
                                                            graph.connect_lifetimes(
                                                                *arg_node,
                                                                lvalue_node,
                                                            );
                                                            matched = true;
                                                        }
                                                    }
                                                    if !matched {
                                                        for (arg_node, _) in args.iter() {
                                                            graph.connect_lifetimes(
                                                                *arg_node,
                                                                lvalue_node,
                                                            );
                                                        }
                                                    }
                                                }
                                            } else {
                                                for (i, arg) in args.iter().enumerate() {
                                                    if let Some(arg_node) = use_operand(
                                                        graph,
                                                        arg,
                                                        loc,
                                                        i as u32,
                                                        &mut usages,
                                                    ) {
                                                        graph.connect_lifetimes(
                                                            arg_node,
                                                            lvalue_node,
                                                        );
                                                    }
                                                }
                                            }
                                        }
                                        hir_ty::CallableDefId::EnumVariantId(_)
                                        | hir_ty::CallableDefId::StructId(_) => {
                                            for (i, arg) in args.iter().enumerate() {
                                                if let Some(arg) = use_operand(
                                                    graph,
                                                    arg,
                                                    loc,
                                                    i as u32,
                                                    &mut usages,
                                                ) {
                                                    graph.connect_lifetimes(arg, lvalue_node);
                                                }
                                            }
                                        }
                                    }
                                }
                                ty => panic!("unhandled callable type {:?}", ty),
                            },
                            _ => panic!("unhandled call op {:?}", func),
                        }

                        Some(NodeStatement::Assignment {
                            assigned,
                            used: usages.into(),
                        })
                    }
                    TerminatorKind::DropAndReplace { place, value, .. } => {
                        let (lvalue_node, assigned) =
                            place_to_lvalue(graph, place, loc, &mut usages);
                        if let Some(op_node) = use_operand(graph, value, loc, 0, &mut usages) {
                            graph.connect_lifetimes(op_node, lvalue_node);
                        }
                        Some(NodeStatement::Assignment {
                            assigned,
                            used: usages.into(),
                        })
                    }
                    TerminatorKind::Assert { cond: value, .. }
                    | TerminatorKind::Yield { value, .. } => {
                        use_operand(graph, value, loc, 0, &mut usages);
                        Some(NodeStatement::Assignment {
                            assigned: smallvec![],
                            used: usages.into(),
                        })
                    }
                    TerminatorKind::SwitchInt { discr, .. } => {
                        // this will always just be a copy of a MIR local, so this is not really needed for the analysis..
                        use_operand(graph, discr, loc, 0, &mut usages);
                        Some(NodeStatement::Assignment {
                            assigned: smallvec![],
                            used: usages.into(),
                        })
                    }
                    _ => None,
                };
                if let Some(statement) = statement {
                    statements.insert(loc, statement);
                }
            }
        }

        // parameter init
        for (param_id, param_loc) in self.param_locations.iter() {
            if *param_id == Self::CAPTURE_LOCAL {
                if let Some(captures) = captures {
                    statements.insert(
                        *param_loc,
                        NodeStatement::Assignment {
                            assigned: captures.into(),
                            used: smallvec![],
                        },
                    );
                    continue;
                }
            }
            let move_path = self.move_data.move_path_for(*param_id);
            statements.insert(
                *param_loc,
                NodeStatement::Assignment {
                    assigned: graph.alloc_path(
                        &self.move_data,
                        move_path,
                        self.path_binding(move_path),
                        self.location_def(*param_loc),
                    ),
                    used: smallvec![],
                },
            );
        }

        Result::Ok(statements)
    }

    fn dependencies(
        &self,
        graph: &mut Graph,
        block_states: &ArenaMap<BasicBlockId, MovePathStates>,
        statements: &ArenaMap<LocationId, NodeStatement>,
    ) {
        for (block_id, _) in self.mir_body.basic_blocks.iter() {
            let mut path_states = block_states[block_id].clone();

            for statement in self.block_locations[block_id]
                .iter()
                .filter_map(|loc| statements.get(loc))
            {
                match statement {
                    NodeStatement::Assignment { assigned, used } => {
                        for (usage_path, usage_kind, usage_node) in used.iter() {
                            if let Some(state) = path_states.get(*usage_path) {
                                for source_node in state.iter_sources() {
                                    graph.connect(source_node, *usage_node, *usage_kind);
                                    graph.connect_lifetimes(source_node, *usage_node);
                                }

                                if let Some(moved_nodes) = &state.moved {
                                    graph.add_conflict(Conflict {
                                        kind: ConflictKind::Moved,
                                        from: *usage_node,
                                        targets: moved_nodes.iter().collect(),
                                    })
                                }

                                // FIXME: something about this analysis is wrong currently..
                                // if state.maybe_uninit {
                                //     graph.add_conflict(Conflict {
                                //         kind: ConflictKind::UseOfMaybeUnassigned,
                                //         from: *usage_node,
                                //         targets: Default::default(),
                                //     })
                                // }

                                if let EdgeKind::Ref {
                                    mutability: true, ..
                                } = usage_kind
                                {
                                    let targets: Vec<_> = state
                                        .iter_sources()
                                        .filter_map(|source| match graph.nodes[source].kind {
                                            NodeKind::Place(binding, _) => binding.and_then(|id| {
                                                (!self.thir_builder.marked_mut(id))
                                                    .then_some(source)
                                            }),
                                            NodeKind::Deref {
                                                lvalue: true,
                                                mutable: false,
                                                ..
                                            } => Some(source),
                                            _ => None,
                                        })
                                        .collect();
                                    if !targets.is_empty() {
                                        graph.conflicts.push(Conflict {
                                            kind: ConflictKind::MutRefToImmutable,
                                            from: *usage_node,
                                            targets,
                                        });
                                    }
                                }
                            } else {
                                graph.add_conflict(Conflict {
                                    kind: ConflictKind::UseOfUnassigned,
                                    from: *usage_node,
                                    targets: Default::default(),
                                });
                            }
                        }
                        for (assigned_path, assigned) in assigned {
                            let assigned_node = &graph[*assigned];
                            if let Some(path_state) = path_states.get(*assigned_path) {
                                match assigned_node.kind {
                                    NodeKind::Deref { mutable, .. } => {
                                        if !mutable {
                                            graph.add_conflict(Conflict {
                                                kind: ConflictKind::AssignToValueBehindImmutableRef,
                                                from: *assigned,
                                                targets: vec![],
                                            });
                                        }

                                        for orig_assign in path_state.iter_sources() {
                                            graph.connect(orig_assign, *assigned, EdgeKind::Deref);
                                            graph.connect_lifetimes(orig_assign, *assigned);
                                        }
                                    }
                                    NodeKind::Place(path, _) => {
                                        if path_state.is_assigned() {
                                            if !path
                                                .map(|binding| {
                                                    self.thir_builder.marked_mut(binding)
                                                })
                                                .unwrap_or(false)
                                            {
                                                graph.add_conflict(Conflict {
                                                    kind: ConflictKind::AssignToImmutable,
                                                    from: *assigned,
                                                    targets: path_state.iter_sources().collect(),
                                                });
                                            }

                                            for orig_assign in path_state.iter_sources() {
                                                // prevent the node from reassigning itself (when inside a loop)
                                                if orig_assign != *assigned {
                                                    graph.connect(
                                                        orig_assign,
                                                        *assigned,
                                                        EdgeKind::Reassign,
                                                    );
                                                }
                                            }
                                        }
                                    }
                                    NodeKind::Value | NodeKind::Drop => {
                                        // FIXME: this should probably be a panic..
                                        println!("Assignment to non-place.");
                                    }
                                }
                            };
                        }
                    }
                    NodeStatement::EndScope { move_path, node } => {
                        // the scope of nodes with lt, should be limited to their last usage
                        if !self.move_data[*move_path].contains_lt() {
                            self.move_data.for_each_child_path(*move_path, |path| {
                                if let Some(state) = path_states.get(path) {
                                    for source_node in state.iter_sources() {
                                        graph.connect(source_node, *node, EdgeKind::EndScope);
                                    }
                                }
                            });
                        }
                    }
                }

                path_states.apply_statement(statement, &self.move_data);
            }
        }
    }

    fn find_lifetimes_in_type_ref(&self, type_ref: &TypeRef) -> Box<[LifetimeRef]> {
        enum T<'a> {
            Type(&'a TypeRef),
            Path(&'a Path),
            ArgsAndBindings(&'a GenericArgs),
            GenericArgs(&'a [GenericArg]),
            Bound(&'a TypeBound),
        }
        let mut lifetimes = vec![];

        let mut stack = vec![T::Type(type_ref)];
        while let Some(top) = stack.pop() {
            match top {
                T::Type(type_ref) => {
                    match type_ref {
                        TypeRef::Tuple(inner_tys) => {
                            stack.extend(inner_tys.iter().map(|ty_ref| T::Type(ty_ref)));
                        }
                        TypeRef::Path(path) => stack.push(T::Path(path)),
                        TypeRef::Reference(inner_ty, lt, _) => {
                            stack.push(T::Type(inner_ty.as_ref()));
                            lifetimes.extend(lt.iter().cloned()); // TODO: add elided lifetime, if non is defined
                        }
                        TypeRef::Array(inner_ty, _)
                        | TypeRef::Slice(inner_ty)
                        | TypeRef::RawPtr(inner_ty, _) => stack.push(T::Type(inner_ty.as_ref())),
                        TypeRef::ImplTrait(bounds) | TypeRef::DynTrait(bounds) => {
                            stack.extend(bounds.iter().map(|bound| T::Bound(bound.as_ref())));
                        }
                        TypeRef::Fn(..) | _ => (),
                    }
                }
                T::Path(path) => {
                    stack.extend(path.type_anchor().map(|ty_ref| T::Type(ty_ref)));
                    for segment in path.segments().iter() {
                        stack.extend(
                            segment
                                .args_and_bindings
                                .map(|args| T::ArgsAndBindings(args)),
                        );
                    }
                }
                T::ArgsAndBindings(args_and_bindings) => {
                    stack.push(T::GenericArgs(args_and_bindings.args.as_ref()));
                    for binding in args_and_bindings.bindings.iter() {
                        stack.extend(binding.type_ref.as_ref().map(|ty_ref| T::Type(ty_ref)));
                        stack.extend(
                            binding
                                .args
                                .as_ref()
                                .map(|args| T::ArgsAndBindings(args.as_ref())),
                        );
                        for bound in binding.bounds.iter() {
                            stack.push(T::Bound(bound.as_ref()));
                        }
                    }
                }
                T::GenericArgs(args) => {
                    for arg in args {
                        match arg {
                            GenericArg::Type(ty_ref) => stack.push(T::Type(ty_ref)),
                            GenericArg::Lifetime(lt) => lifetimes.push(lt.clone()),
                            GenericArg::Const(_) => (),
                        }
                    }
                }
                T::Bound(bound) => {
                    match bound {
                        TypeBound::Path(path, _) => stack.push(T::Path(path)),
                        TypeBound::Lifetime(lt) => lifetimes.push(lt.clone()),
                        TypeBound::ForLifetime(_, _) => {
                            panic!("type bound ForLifetime not implemented.");
                        } // where is this used?
                        TypeBound::Error => (),
                    }
                }
            }
        }
        lifetimes.into_boxed_slice()
    }

    fn location_def(&self, location: LocationId) -> Option<DefId> {
        self.locations[location].0
    }

    fn place_binding(&self, place: &Place) -> Option<BindingId> {
        if let Some(binding) = self.local_bindings.get(place.local).copied() {
            return Some(binding);
        }

        if place.local == Self::CAPTURE_LOCAL {
            let projections = place.projection.lookup(&self.mir_body.projection_store);
            let mut ty = self.mir_body.locals[place.local].ty.clone();
            let mut last_binding = None;
            for proj in projections {
                ty = proj.projected_ty(
                    ty,
                    self.db,
                    |c, subst, f| {
                        let InternedClosure(def, ..) = self.db.lookup_intern_closure(c.into());
                        let infer = self.db.infer(def);
                        let (captures, _) = infer.closure_info(&c);
                        let capture = captures.get(f).expect("broken closure field");
                        last_binding = Some(capture.local()); // remember the id of the last binding while walking through the captures
                        capture.ty(subst)
                    },
                    self.crate_id,
                );
            }
            return last_binding.map(|hir_id| self.thir_builder.map_binding(hir_id));
        }
        None
    }

    fn find_op_usage(
        &self,
        location: LocationId,
        place: &Place,
        hint: BindingUsageHint,
    ) -> Option<DefId> {
        self.location_def(location).and_then(|def| {
            if let Some(binding) = self.place_binding(place) {
                if let Some(binding_def) = self.thir_builder.find_binding_usage(def, binding, hint)
                {
                    return Some(binding_def);
                }
            }
            None
        })
    }

    fn find_usage(&self, location: LocationId, place: &Place) -> Option<DefId> {
        self.find_op_usage(location, place, BindingUsageHint::None)
    }

    fn find_assignment(&self, location: LocationId, binding: BindingId) -> Option<DefId> {
        self.location_def(location)
            .and_then(|def| self.thir_builder.find_binding_assignment(def, binding))
    }

    fn find_index_usage(&self, path_def: DefId, index: LocalId) -> Option<DefId> {
        if let Some(index_binding) = self.local_bindings.get(index) {
            // find index binding in given path
            let mut child_ids = vec![path_def];
            while let Some(child_id) = child_ids.pop() {
                if let Def::Expr(Expr::Index { index_expr, .. }) = self.thir_builder[child_id] {
                    if self
                        .thir_builder
                        .find_binding_usage(index_expr, *index_binding, BindingUsageHint::None)
                        .is_some()
                    {
                        return Some(index_expr);
                    }
                }
                if let Some(child_defs) = self.thir_builder.child_defs(child_id) {
                    child_ids.extend_from_slice(child_defs);
                }
            }
        }
        None
    }

    fn find_path(&self, binding_def: DefId) -> DefId {
        let mut path_def = binding_def;
        while let Some(parent_def) = self.thir_builder.parent_def(path_def) {
            match self.thir_builder[parent_def] {
                Def::Expr(
                    Expr::Path(_)
                    | Expr::Field { .. }
                    | Expr::UnaryOp {
                        op: UnaryOp::Deref, ..
                    }
                    | Expr::Index { .. },
                ) => {
                    path_def = parent_def;
                }
                _ => break,
            }
        }
        path_def
    }

    fn iter_basic_block_ids(&self) -> impl DoubleEndedIterator<Item = BasicBlockId> + '_ {
        self.mir_body.basic_blocks.iter().map(|(id, _)| id)
    }

    fn basic_block_sequence(&self) -> ArenaMap<BasicBlockId, SmallVec<[BasicBlockId; 1]>> {
        let mut map: ArenaMap<_, SmallVec<[BasicBlockId; 1]>> = self
            .mir_body
            .basic_blocks
            .iter()
            .map(|(id, _)| (id, Default::default()))
            .collect();
        for (id, block) in self.mir_body.basic_blocks.iter() {
            let mut set = |targets: &[BasicBlockId]| {
                map.entry(id).or_default().extend_from_slice(targets);
            };
            if let Some(terminator) = &block.terminator {
                match &terminator.kind {
                    TerminatorKind::SwitchInt { targets, .. } => {
                        set(targets.all_targets());
                    }
                    TerminatorKind::Drop { target, .. }
                    | TerminatorKind::Goto { target }
                    | TerminatorKind::DropAndReplace { target, .. }
                    | TerminatorKind::Assert { target, .. }
                    | TerminatorKind::Yield { resume: target, .. }
                    | TerminatorKind::FalseEdge {
                        real_target: target,
                        ..
                    }
                    | TerminatorKind::FalseUnwind {
                        real_target: target,
                        ..
                    } => {
                        set(&[*target]);
                    }
                    TerminatorKind::Call { target, .. } => {
                        if let Some(target) = target {
                            set(&[*target]);
                        }
                    }
                    TerminatorKind::UnwindResume
                    | TerminatorKind::Abort
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable
                    | TerminatorKind::CoroutineDrop => (),
                }
            }
        }
        map
    }

    fn basic_block_sequence_inv(
        &self,
        sequence: &ArenaMap<BasicBlockId, SmallVec<[BasicBlockId; 1]>>,
    ) -> ArenaMap<BasicBlockId, SmallVec<[BasicBlockId; 1]>> {
        let mut map: ArenaMap<_, SmallVec<[BasicBlockId; 1]>> = self
            .iter_basic_block_ids()
            .map(|id| (id, Default::default()))
            .collect();
        for (id, targets) in sequence.iter() {
            for target in targets.iter() {
                map.entry(*target).or_default().push(id);
            }
        }
        map
    }
}
