use std::{
    fmt::{Debug, Display},
    ops::Not,
};

use bitvec::{order::Lsb0, vec::BitVec};
use la_arena::{Arena, ArenaMap, Idx, RawIdx};
use smallvec::SmallVec;

mod operators;

pub use operators::*;

use serde::{Deserialize, Serialize};

// TODO: better name.. Def for Body-Definition
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Def {
    Expr(Expr),
    Pat(Pat),
    Noop,
}
pub type DefId = Idx<Def>;

impl Def {
    pub fn precedence(&self) -> i32 {
        // https://doc.rust-lang.org/reference/expressions.html
        match self {
            Def::Expr(expr) => match expr {
                Expr::Path(_)
                | Expr::Literal(_)
                | Expr::RecordLit { .. }
                | Expr::Tuple { .. }
                | Expr::Array(_) => 190,
                Expr::MethodCall { .. } => 180,
                Expr::Field { .. } => 170,
                Expr::Call { .. } | Expr::Index { .. } => 160,
                Expr::Ref { .. } | Expr::UnaryOp { .. } => 150,
                Expr::BinaryOp { op, .. } => match op {
                    BinaryOp::ArithOp(arith) => match arith {
                        ArithOp::Mul | ArithOp::Div | ArithOp::Rem => 140,
                        ArithOp::Add | ArithOp::Sub => 130,
                        ArithOp::Shl | ArithOp::Shr => 120,
                        ArithOp::BitAnd => 110,
                        ArithOp::BitXor => 100,
                        ArithOp::BitOr => 90,
                    },
                    BinaryOp::CmpOp(_) => 80,
                    BinaryOp::LogicOp(logic) => match logic {
                        LogicOp::And => 70,
                        LogicOp::Or => 60,
                    },
                    BinaryOp::Assignment { .. } => 40,
                },
                Expr::Range { .. } => 50,
                _ => 0,
            },
            _ => 0,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Binding {
    Real { name: String, marked_mutable: bool },
    Fake,
}
impl Binding {
    pub fn name(&self) -> &str {
        match self {
            Binding::Real { name, .. } => &name,
            Binding::Fake => "Fake",
        }
    }
}
pub type BindingId = Idx<Binding>;

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum PathInfo {
    Binding(BindingId),
    Path(String),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum Mutability {
    Shared,
    Mut,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CaptureBy {
    /// `move |x| y + x`.
    Value,
    /// `move` keyword was not specified.
    Ref,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Expr {
    Path(PathInfo),
    Literal(String),
    Block {
        statements: Vec<Statement>,
        tail: Option<DefId>,
        scope_start: DefId,
        scope_end: DefId,
    },
    If {
        condition: DefId,
        then_branch: DefId,
        else_branch: Option<DefId>,
    },
    Let {
        pat: DefId,
        expr: DefId,
    },
    Match {
        expr: DefId,
        arms: Vec<MatchArm>,
    },
    Ref {
        expr: DefId,
        mutability: Mutability,
    },
    UnaryOp {
        expr: DefId,
        op: UnaryOp,
    },
    BinaryOp {
        lhs: DefId,
        rhs: DefId,
        op: BinaryOp,
    },
    Call {
        callee: DefId,
        args: Vec<DefId>,
    },
    MethodCall {
        receiver: DefId,
        fn_name: String,
        args: Vec<DefId>,
    },
    Field {
        expr: DefId,
        field: String,
    },
    Loop {
        body: DefId,
        label: Option<String>,
    },
    Index {
        base: DefId,
        index_expr: DefId,
    },
    Range {
        lhs: Option<DefId>,
        rhs: Option<DefId>,
        inclusive: bool,
    },
    RecordLit {
        path: String,
        fields: Vec<(String, DefId)>,
        spread: Option<DefId>,
        ellipsis: bool,
    },
    Return {
        expr: Option<DefId>,
    },
    Tuple {
        exprs: Vec<DefId>,
    },
    Closure {
        capture_binding: BindingId,
        capture_dummy: DefId,
        args: Vec<DefId>,
        body_expr: DefId,
        capture_by: CaptureBy,
        return_dummy: DefId,
        return_binding: BindingId,
    },
    Array(Array),
    Box {
        expr: DefId,
    },
    Break {
        expr: Option<DefId>,
        label: Option<String>,
    },
    Continue {
        label: Option<String>,
    },
    Missing,
    Unimplemented,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Pat {
    Wild,
    Path(String),
    Lit(DefId),
    Bind {
        annotation: Option<BindingAnnotation>,
        binding_id: BindingId,
        subpat: Option<DefId>,
    },
    Ref {
        pat: DefId,
        mutability: Mutability,
    },
    Or {
        patterns: Vec<DefId>,
    },
    Tuple {
        pats: Vec<DefId>,
        dots: Option<usize>,
    },
    Record {
        path: String,
        args: Vec<(String, DefId)>,
        ellipsis: bool,
    },
    TupleStruct {
        path: String,
        args: Vec<DefId>,
        ellipsis: Option<usize>,
    },
    Unimplemented,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
pub enum BindingAnnotation {
    Mutable,
    Ref,
    RefMut,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Statement {
    Let {
        pat: DefId,
        type_ref: Option<String>,
        initializer: Option<DefId>,
        else_branch: Option<DefId>,
    },
    Expr {
        expr: DefId,
    },
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct MatchArm {
    pub pat: DefId,
    pub guard: Option<DefId>,
    pub expr: DefId,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Array {
    ElementList { elements: Vec<DefId> },
    Repeat { initializer: DefId, repeat: DefId },
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum DependencyKind {
    Ref(bool),
    Move,
    Copy,
    Deref,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefSet {
    def_map: BitVec<u32, Lsb0>,
}

impl std::ops::Index<DefId> for DefSet {
    type Output = bool;
    fn index(&self, index: DefId) -> &Self::Output {
        &self.def_map[index.into_raw().into_u32() as usize]
    }
}

impl DefSet {
    pub fn new(defs: &Arena<Def>) -> Self {
        Self {
            def_map: BitVec::repeat(false, defs.len()),
        }
    }

    pub fn new_true(defs: &Arena<Def>) -> Self {
        Self {
            def_map: BitVec::repeat(true, defs.len()),
        }
    }

    pub fn and(&mut self, other: &Self) {
        assert!(self.def_map.len() == other.def_map.len());
        self.def_map &= &other.def_map;
        // for (mut a, b) in self.def_map.iter_mut().zip(other.def_map.iter()) {
        //     a.set(*a && *b);
        // }
    }

    pub fn or(&mut self, other: &Self) {
        assert!(self.def_map.len() == other.def_map.len());
        self.def_map |= &other.def_map;
        // for (mut a, b) in self.def_map.iter_mut().zip(other.def_map.iter()) {
        //     a.set(*a || *b);
        // }
    }

    pub fn inverted(&mut self) -> Self {
        Self {
            def_map: !self.def_map.clone(),
        }
    }

    pub fn set(&mut self, def_id: DefId, value: bool) {
        self.def_map
            .set(def_id.into_raw().into_u32() as usize, value);
    }

    pub fn iter(&self) -> impl Iterator<Item = (DefId, bool)> + '_ {
        self.def_map
            .iter()
            .enumerate()
            .map(|(index, active)| (DefId::from_raw(RawIdx::from_u32(index as u32)), *active))
    }

    pub fn contains(&self, def_id: DefId) -> bool {
        self.def_map
            .get(def_id.into_raw().into_u32() as usize)
            .map(|bit| *bit)
            .unwrap_or(false)
    }

    pub fn any(&self) -> bool {
        self.def_map.any()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DataFlowTree {
    pub binding: BindingId,
    pub initialization: Vec<DefId>,
    pub usages: Vec<(DefId, DependencyKind, SmallVec<[DataFlowTreeId; 1]>)>,
    pub liveliness: DefSet,
    pub is_mut: bool,
    pub has_ref: bool,
}
pub type DataFlowTreeId = Idx<DataFlowTree>;

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum ConflictKind {
    Moved,
    AssignToImmutable,
    AssignToValueBehindImmutableRef,
    MoveOutOfRef,
    UseOfUnassigned,
    MutRefToImmutable,
}

impl Display for ConflictKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            ConflictKind::Moved => "Use of moved value.",
            ConflictKind::AssignToImmutable => "Assignment to immutable binding.",
            ConflictKind::AssignToValueBehindImmutableRef => {
                "Assignment to a value, which lies behind an immutable reference."
            }
            ConflictKind::MoveOutOfRef => "Move out of reference.",
            ConflictKind::UseOfUnassigned => "Use of unassigned value.",
            ConflictKind::MutRefToImmutable => {
                "Creating an mutable reference to an immutable value."
            }
        })
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Conflict {
    pub kind: ConflictKind,
    pub targets: Vec<DefId>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct DataFlowInfo {
    pub tree: Arena<DataFlowTree>,
    pub def_map: ArenaMap<DefId, SmallVec<[DataFlowTreeId; 1]>>,
    pub conflicts: Vec<Conflict>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MacroResugaring {
    pub call: String,
    pub child_defs: Vec<DefId>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ForLoopResugaring {
    pub pat: DefId,
    pub iterable: DefId,
    pub body: DefId,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WhileLoopResugaring {
    pub condition: DefId,
    pub body: DefId,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QuestionMarkResugaring {
    pub expr: DefId,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Resugaring {
    Macro(MacroResugaring),
    ForLoop(ForLoopResugaring),
    WhileLoop(WhileLoopResugaring),
    QuestionMark(QuestionMarkResugaring),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThirBody {
    pub name: String,
    pub params: Vec<(DefId, String)>,
    pub return_type: (DefId, String),
    pub body_expr: DefId,

    pub defs: Arena<Def>,
    pub bindings: Arena<Binding>,

    pub next_def_map: ArenaMap<DefId, DefId>,
    pub never_defs: DefSet,
    pub selectable_defs: DefSet,
    pub def_order: ArenaMap<DefId, u32>,

    pub expr_resugaring: ArenaMap<DefId, Resugaring>,

    pub def_graph: ArenaMap<DefId, DefNode>,
    pub def_graph_inv: ArenaMap<DefId, SmallVec<[DefId; 1]>>,
    pub conflicts: ArenaMap<DefId, Vec<Conflict>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum NodeKind {
    Source {
        binding: BindingId,
        mutable: bool,
        contains_lt: bool,
    },
    Usage,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DefEdgeKind {
    Move(bool), // partial
    Copy,
    Ref(bool),
    Reassign,
    ReassignSource,
    Deref,
    Lifetime,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DefNode {
    pub kind: NodeKind,
    pub edges: Vec<(DefEdgeKind, DefId)>,
    pub active: DefSet,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExampleState {
    pub body: ThirBody,
    pub selected: Option<DefId>,
}
