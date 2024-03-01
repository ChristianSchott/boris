use std::{
    collections::HashMap,
    f32::consts::PI,
    ops::{BitAnd, BitOr, Not},
    sync::Arc,
};

use bitvec::{prelude::BitArray, prelude::Lsb0};
use boris_shared::{
    BinaryOp, BindingAnnotation, BindingId, Conflict, Def, DefId, DefSet, DefSpan, Mutability,
    UnaryOp,
};
use eframe::{
    egui::{self, Margin, Painter},
    emath::Align::Min,
    epaint::{
        pos2, text::LayoutJob, vec2, Color32, CubicBezierShape, FontId, Galley, Pos2,
        QuadraticBezierShape, Rect, Rounding, Shape, Stroke, Vec2,
    },
};
use egui::{
    epaint::{Hsva, PathShape},
    Align2,
};
use itertools::Itertools;
use la_arena::{Arena, ArenaMap, Idx};
use tuple::{self, Map};

use crate::view::Tree;

#[derive(Debug, Clone, Copy, Default)]
pub struct Liveliness(BitArray<[u32; 1], Lsb0>);
impl Liveliness {
    pub const ZERO: Self = Self(BitArray::ZERO);

    pub fn set(&mut self, index: LaneIndex, value: bool) {
        self.0.set(index.0 as usize, value);
    }

    pub fn is_live(&self, index: LaneIndex) -> bool {
        self.0[index.0 as usize]
    }

    pub fn iter_live(&self) -> impl Iterator<Item = LaneIndex> + '_ {
        self.0
            .iter_ones()
            .map(|live| LaneIndex::from_raw(live as u32))
    }

    pub fn live_lanes(&self) -> Box<[LaneIndex]> {
        Box::from_iter(self.iter_live())
    }

    pub fn live_count(&self) -> u32 {
        self.0.count_ones() as u32
    }

    pub fn and(&self, other: &Self) -> Self {
        Self(self.0.bitand(other.0))
    }

    pub fn or(&self, other: &Self) -> Self {
        Self(self.0.bitor(other.0))
    }

    pub fn inverted(&self) -> Self {
        Self(self.0.not())
    }

    pub fn index_for(&self, lane: LaneIndex) -> u32 {
        (self.0.split_at(lane.0 as usize).0.count_ones() + 1) as u32
    }

    // FIXME: for now we just consider lines as locked, if there is a higher-order line active (higher lane index)
    pub fn is_locked(&self, lane: LaneIndex) -> bool {
        self.0.split_at(lane.0 as usize).1.count_ones() > 1 // split index is included in the right slice, thus > 1
    }
}

#[derive(Clone, Copy, Debug)]
pub enum UsageKind {
    Move(bool), // partial
    Copy,
    Reference(bool), // mutability
    Deref,
}

#[derive(Debug, Clone)]
pub struct DefLivelinessInfo {
    def_liveliness: Box<[Liveliness]>, // which lanes are active for each def_id
    lane_binding: Box<[(f32, bool, bool, Option<DefId>)]>,
    active_defs: ArenaMap<DefId, (Vec<LaneIndex>, Vec<(LaneIndex, UsageKind)>)>, // assignments & usages
    used: u32,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LaneIndex(u32);
impl LaneIndex {
    fn from_raw(index: u32) -> Self {
        LaneIndex(index)
    }
}

impl DefLivelinessInfo {
    pub fn new(defs: &Arena<Def>, trees: &[Tree], never_defs: &DefSet) -> DefLivelinessInfo {
        assert!(Liveliness::ZERO.0.len() >= trees.len()); // ensure bit-array has enough capacity
        let lane = |index: usize| LaneIndex::from_raw(index as u32);

        let mut active_defs: ArenaMap<DefId, (Vec<LaneIndex>, Vec<(LaneIndex, UsageKind)>)> =
            ArenaMap::new();
        for (index, tree) in trees.iter().enumerate() {
            for assign_def in tree.assignments.iter() {
                let (assignments, _) = active_defs.entry(*assign_def).or_default();
                assignments.push(lane(index));
            }
            for (kind, usage_def) in tree.usages.iter() {
                let (_, usages) = active_defs.entry(*usage_def).or_default();
                usages.push((lane(index), *kind));
            }
        }

        let mut info = DefLivelinessInfo {
            def_liveliness: Box::from_iter(std::iter::repeat(Liveliness::ZERO).take(defs.len())),
            active_defs,
            used: trees.len() as u32,
            lane_binding: Box::from_iter(trees.iter().map(|tree| {
                (
                    Self::hash(tree.binding),
                    tree.mutable,
                    tree.activity().any(),
                    tree.scope,
                )
            })),
        };
        for (index, tree) in trees.iter().enumerate() {
            let index = lane(index);
            for (def_id, active) in tree.activity().iter() {
                info.def_liveliness[def_id.into_raw().into_u32() as usize].set(index, active);
            }
        }
        // TODO: disable never defs..
        info
    }

    pub fn lane_for_def(&self, def_id: DefId) -> Option<LaneIndex> {
        self.active_defs.get(def_id).and_then(|(assigns, usages)| {
            assigns
                .first()
                .copied()
                .or_else(|| usages.first().map(|(lane, _)| *lane))
        })
    }

    pub fn assignments_for(&self, def_id: DefId) -> Option<&[LaneIndex]> {
        self.active_defs
            .get(def_id)
            .map(|(assignments, _)| -> &[LaneIndex] { &assignments })
    }

    pub fn usages_for(&self, def_id: DefId) -> Option<&[(LaneIndex, UsageKind)]> {
        self.active_defs
            .get(def_id)
            .map(|(_, usages)| -> &[(LaneIndex, UsageKind)] { &usages })
    }

    pub fn has_activity(&self, def_id: DefId) -> bool {
        self.active_defs.contains_idx(def_id)
    }

    pub fn active_count_for(&self, def_id: DefId) -> usize {
        self.active_defs
            .get(def_id)
            .map(|(assignments, usages)| assignments.len() + usages.len())
            .unwrap_or(0)
    }

    pub fn is_live(&self, def_id: DefId, index: LaneIndex) -> bool {
        assert!(index.0 <= self.used);
        self.def_liveliness[def_id.into_raw().into_u32() as usize].is_live(index)
    }

    pub fn live_at(&self, def_id: DefId) -> Box<[LaneIndex]> {
        self.def_liveliness[def_id.into_raw().into_u32() as usize].live_lanes()
    }

    pub fn count_live_at(&self, def_id: DefId) -> u32 {
        self.def_liveliness[def_id.into_raw().into_u32() as usize].live_count()
    }

    pub fn liveliness_at(&self, def_id: DefId) -> Liveliness {
        self.def_liveliness[def_id.into_raw().into_u32() as usize]
    }

    pub fn liveliness_for(&self, span: DefSpan) -> Liveliness {
        self.liveliness_at(span.from)
            .and(&self.liveliness_at(span.to))
    }

    pub fn is_lane_mut(&self, index: LaneIndex) -> bool {
        self.lane_binding[index.0 as usize].1
    }

    pub fn is_lane_active(&self, index: LaneIndex) -> bool {
        self.lane_binding[index.0 as usize].2
    }

    pub fn lane_owner(&self, index: LaneIndex) -> Option<DefId> {
        self.lane_binding[index.0 as usize].3
    }

    // return type `Liveliness` is a bit misleading here.. as it is more of a LaneMask
    pub fn lanes_for_owner(&self, owner: DefId) -> Liveliness {
        let mut mask = Liveliness::default();
        for (lane, (.., lane_owner)) in self.lane_binding.iter().enumerate() {
            mask.set(LaneIndex::from_raw(lane as u32), *lane_owner == Some(owner));
        }
        mask
    }

    fn hash(binding: BindingId) -> f32 {
        const OFFSET: f32 = -PI * 0.5f32;
        const MUL: f32 = 42f32;
        let id = binding.into_raw().into_u32();
        ((id as f32 * MUL + OFFSET).sin() + 1.) / 2f32
    }

    pub fn color(&self, index: LaneIndex) -> Color32 {
        Hsva::new(self.lane_binding[index.0 as usize].0, 1.0f32, 0.65f32, 1f32).into()
    }

    pub fn locked_color(&self, index: LaneIndex) -> Color32 {
        Hsva::new(self.lane_binding[index.0 as usize].0, 0.95f32, 0.4f32, 1f32).into()
    }

    pub fn stroke(&self, locked: bool, index: LaneIndex) -> Stroke {
        self.raw_stroke(index, locked, self.is_lane_mut(index))
    }

    pub fn raw_stroke(&self, index: LaneIndex, locked: bool, mutable: bool) -> Stroke {
        Stroke::new(
            mutable.then_some(2f32).unwrap_or(1f32) * DrawBuffer::LINE_WIDTH,
            locked
                .then_some(self.locked_color(index))
                .unwrap_or_else(|| self.color(index)),
        )
    }
}

#[derive(Clone)]
pub struct State {
    pub selected: Vec<DefId>,
    pub liveliness: DefLivelinessInfo,

    // FIXME: this does not belong in here..
    pub order: ArenaMap<DefId, u32>,
    pub first_def: ArenaMap<DefId, DefId>,
}

impl State {
    pub fn new(
        selected: Vec<DefId>,
        liveliness: DefLivelinessInfo,
        order: ArenaMap<DefId, u32>,
        first_def: ArenaMap<DefId, DefId>,
    ) -> Self {
        Self {
            selected,
            liveliness,
            order,
            first_def,
        }
    }
}

#[derive(Clone, Debug)]
pub enum CFKind {
    // TODO: Box<[]> the vecs
    // TODO: make real types out of these tuples..
    Line(
        Vec<(LaneIndex, RelativeDrawCallId, DefId, bool)>, // assignments
        Vec<(LaneIndex, RelativeDrawCallId, DefId, UsageKind, bool)>, // usages
    ), // active defs
    Closure(Vec<(LaneIndex, RelativeDrawCallId, DefId, UsageKind, bool)>), // active defs
    Branch(
        Box<[(RelativeDrawCallId, DefSpan)]>,
        bool, /* full defer? */
    ),
}

impl CFKind {
    fn offset(&self, offset: Vec2) -> CFKind {
        fn offset_usages(
            from: &[(LaneIndex, RelativeDrawCallId, DefId, UsageKind, bool)],
            offset: Vec2,
        ) -> Vec<(LaneIndex, RelativeDrawCallId, DefId, UsageKind, bool)> {
            from.iter()
                .map(|(lane, call, id, kind, handled)| {
                    (*lane, call.offset(offset), *id, *kind, *handled)
                })
                .collect_vec()
        }

        match self {
            CFKind::Branch(branches, full) => CFKind::Branch(
                Box::from_iter(
                    branches
                        .iter()
                        .map(|(call, span)| (call.offset(offset), *span)),
                ),
                *full,
            ),
            CFKind::Closure(captures) => CFKind::Closure(offset_usages(&captures, offset)),
            CFKind::Line(assignment, usages) => CFKind::Line(
                assignment
                    .iter()
                    .map(|(lane, call, id, handled)| (*lane, call.offset(offset), *id, *handled))
                    .collect_vec(),
                offset_usages(&usages, offset),
            ),
        }
    }

    fn filter(&self, handled: Liveliness) -> CFKind {
        // this is just ugly, but it works..
        match self {
            CFKind::Line(assigned, used) => CFKind::Line(
                assigned
                    .iter()
                    .cloned()
                    .map(|mut usage| {
                        usage.3 |= handled.is_live(usage.0);
                        usage
                    })
                    .collect_vec(),
                used.iter()
                    .cloned()
                    .map(|mut usage| {
                        usage.4 |= handled.is_live(usage.0);
                        usage
                    })
                    .collect_vec(),
            ),
            CFKind::Closure(captures) => CFKind::Closure(
                captures
                    .iter()
                    .cloned()
                    .map(|mut usage| {
                        usage.4 |= handled.is_live(usage.0);
                        usage
                    })
                    .collect_vec(),
            ),
            kind => kind.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CFSections {
    liveliness: Liveliness,
    sections: Box<[(f32, Liveliness, CFKind)]>,
}

impl CFSections {
    fn iter(
        &self,
        origin: Pos2,
        offset: Vec2,
    ) -> impl Iterator<Item = (CFKind, Liveliness, Liveliness, Pos2, Pos2)> + '_ {
        self.sections.iter().scan(
            (0f32, self.liveliness),
            move |(start_y, from_liveliness), (end_y, liveliness, kind)| {
                let ret = (
                    kind.offset(origin.to_vec2() + offset),
                    from_liveliness.clone(),
                    liveliness.clone(),
                    origin + offset + Vec2::DOWN * *start_y,
                    origin + offset + Vec2::DOWN * *end_y,
                );
                *start_y = *end_y;
                *from_liveliness = *liveliness;
                Some(ret)
            },
        )
    }
}

#[derive(Default, Clone, Debug)]
pub enum DrawCallKind {
    Text(Arc<Galley>, Color32),
    Rect(Color32, Rounding),
    Bracketed(BracketType, Color32, f32),

    Inline(Box<[RelativeDrawCallId]>),
    Branch(Box<[RelativeDrawCallId]>, DefSpan, bool),
    Sequential(Box<[RelativeDrawCallId]>),
    ControlFlow(CFSections, RelativeDrawCallId, Option<DefId>),
    Closure(DrawCallId, DefId),

    Alias(DrawCallId, Box<[DefId]>),

    #[default]
    Noop,
}

#[derive(Default)]
pub struct DrawCall {
    pub kind: DrawCallKind,
    pub size: Vec2,
}
pub type DrawCallId = Idx<DrawCall>;

#[derive(Clone, Copy, Debug)]
pub struct RelativeDrawCallId {
    pub id: DrawCallId,
    pub offset: Vec2,
}
impl RelativeDrawCallId {
    pub fn new(id: DrawCallId, offset: Vec2) -> Self {
        Self { id, offset }
    }
    pub fn root(id: DrawCallId) -> Self {
        Self {
            id,
            offset: Vec2::ZERO,
        }
    }
    pub fn offset(&self, offset: Vec2) -> RelativeDrawCallId {
        Self {
            offset: self.offset + offset,
            ..*self
        }
    }
}
impl From<(Vec2, DrawCallId)> for RelativeDrawCallId {
    fn from(value: (Vec2, DrawCallId)) -> Self {
        Self {
            id: value.1,
            offset: value.0,
        }
    }
}

enum TreeWalkerState<T> {
    DescendToChildren,
    Continue,
    Stop,
    Return(T),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum TextLitKind {
    Comma,
    Dot,
    Dots,
    Semi,
    Let,
    For,
    In,
    If,
    Then,
    Else,
    Match,
    While,
    Loop,
    Space,
    Tab,
    At,
    Return,
    Break,
    Continue,
    Tick,
    Colon,
    Under,
    Move,
    Box,
    Fn,
    Arrow,
    WideArrow,
    Range(bool),
    BinaryOp(BinaryOp),
    UnaryOp(UnaryOp),
    Ref(Mutability),
    BindingAnnotation(BindingAnnotation),
    RoundBracket(bool),
    SquareBracket(bool),
    CurlyBracket(bool),
    Pipe,
    QuestionMark,
}

pub struct DrawBuffer<'a> {
    ctx: &'a egui::Context,
    buffer: Arena<DrawCall>,
    def_map: ArenaMap<DrawCallId, (DefId, bool)>, // bool flag, for indicating 'fake' associations (e.g. the for label is not by itself a def, but should be clickable)
    call_complexity: ArenaMap<DrawCallId, bool>,
    text_lit_drawers: HashMap<TextLitKind, DrawCallId>,
    noop_drawer: Option<DrawCallId>,
}

impl<'a> DrawBuffer<'a> {
    const LINE_WIDTH: f32 = 1f32;
    const LINE_SEP: f32 = 5f32;

    pub fn new(ctx: &'a egui::Context) -> Self {
        Self {
            ctx,
            buffer: Arena::new(),
            def_map: ArenaMap::default(),
            call_complexity: ArenaMap::default(),
            text_lit_drawers: Default::default(),
            noop_drawer: None,
        }
    }

    fn append(&mut self, draw_call: DrawCall) -> DrawCallId {
        let is_complex = match &draw_call.kind {
            DrawCallKind::Branch(..)
            | DrawCallKind::Sequential(..)
            | DrawCallKind::ControlFlow(..) => true,
            _ => false,
        };
        let id = self.buffer.alloc(draw_call);

        // is complex itself, or contains any complex draw calls in its direct children
        let complex_child = || -> bool {
            self.walk_children(id, &mut |call| {
                if let Some(is_complex) = self.call_complexity.get(call.id) {
                    if *is_complex {
                        TreeWalkerState::Return(())
                    } else {
                        TreeWalkerState::Continue
                    }
                } else {
                    TreeWalkerState::DescendToChildren
                }
            })
            .is_some()
        };
        self.call_complexity
            .insert(id, is_complex || complex_child());
        id
    }

    pub fn assoc_def_id(&mut self, call_id: DrawCallId, def_id: DefId) {
        if self.def_map.insert(call_id, (def_id, false)).is_some() {
            println!("Double associate Def: {:?}", self.buffer[call_id].kind);
        }
    }

    pub fn fake_assoc_def_id(&mut self, call_id: DrawCallId, def_id: DefId) {
        if self.def_map.insert(call_id, (def_id, true)).is_some() {
            println!("Double associate Def: {:?}", self.buffer[call_id].kind);
        }
    }

    pub fn append_literal(&mut self, kind: TextLitKind) -> DrawCallId {
        const SYMBOL_COLOR: Color32 = Color32::BLACK;
        const KEYWORD_COLOR: Color32 = Color32::DARK_BLUE;
        let mut append_lit = |lit: &str, color: Color32| {
            let galley = text_literal(self.ctx, lit);
            let size = galley.size();
            self.append(DrawCall {
                kind: DrawCallKind::Text(galley, color),
                size,
            })
        };
        // FIXME: consistent use of space vs no-space
        match kind {
            TextLitKind::Comma => append_lit(", ", SYMBOL_COLOR),
            TextLitKind::Dot => append_lit(".", SYMBOL_COLOR),
            TextLitKind::Dots => append_lit("…", SYMBOL_COLOR),
            TextLitKind::Semi => append_lit(";", SYMBOL_COLOR),
            TextLitKind::QuestionMark => append_lit("?", SYMBOL_COLOR),
            TextLitKind::Let => append_lit("let ", KEYWORD_COLOR),
            TextLitKind::For => append_lit("for ", KEYWORD_COLOR),
            TextLitKind::In => append_lit(" in ", KEYWORD_COLOR),
            TextLitKind::If => append_lit("if ", KEYWORD_COLOR),
            TextLitKind::Then => append_lit("then", KEYWORD_COLOR),
            TextLitKind::Else => append_lit("else", KEYWORD_COLOR),
            TextLitKind::Match => append_lit("match ", KEYWORD_COLOR),
            TextLitKind::While => append_lit("while ", KEYWORD_COLOR),
            TextLitKind::Loop => append_lit("loop", KEYWORD_COLOR),
            TextLitKind::Move => append_lit("move ", KEYWORD_COLOR),
            TextLitKind::Box => append_lit("box ", KEYWORD_COLOR),
            TextLitKind::Fn => append_lit("fn ", KEYWORD_COLOR),
            TextLitKind::Space => append_lit(" ", SYMBOL_COLOR),
            TextLitKind::Tab => append_lit("\t", SYMBOL_COLOR),
            TextLitKind::At => append_lit(" @ ", SYMBOL_COLOR),
            TextLitKind::Under => append_lit("_", SYMBOL_COLOR),
            TextLitKind::Arrow => append_lit("-> ", SYMBOL_COLOR),
            TextLitKind::WideArrow => append_lit(" =>", SYMBOL_COLOR),
            TextLitKind::BinaryOp(op) => append_lit(&format!(" {} ", op), SYMBOL_COLOR),
            TextLitKind::UnaryOp(op) => append_lit(
                match op {
                    UnaryOp::Deref => "*",
                    UnaryOp::Not => "!",
                    UnaryOp::Neg => "-",
                },
                SYMBOL_COLOR,
            ),
            TextLitKind::Ref(mutable) => append_lit(
                match mutable {
                    Mutability::Shared => "&",
                    Mutability::Mut => "&mut ",
                },
                SYMBOL_COLOR,
            ),
            TextLitKind::BindingAnnotation(annotation) => match annotation {
                BindingAnnotation::Mutable => append_lit("mut ", KEYWORD_COLOR),
                BindingAnnotation::Ref => append_lit("ref ", KEYWORD_COLOR),
                BindingAnnotation::RefMut => append_lit("ref mut ", KEYWORD_COLOR),
            },
            TextLitKind::Return => append_lit("return", KEYWORD_COLOR),
            TextLitKind::Break => append_lit("break ", KEYWORD_COLOR),
            TextLitKind::Tick => append_lit("'", SYMBOL_COLOR),
            TextLitKind::Colon => append_lit(":", SYMBOL_COLOR),
            TextLitKind::Range(inclusive) => {
                append_lit(if inclusive { "..=" } else { ".." }, SYMBOL_COLOR)
            }
            TextLitKind::Continue => append_lit("continue", KEYWORD_COLOR),
            TextLitKind::RoundBracket(open) => {
                if open {
                    append_lit("(", SYMBOL_COLOR)
                } else {
                    append_lit(")", SYMBOL_COLOR)
                }
            }
            TextLitKind::SquareBracket(open) => {
                if open {
                    append_lit("[", SYMBOL_COLOR)
                } else {
                    append_lit("]", SYMBOL_COLOR)
                }
            }
            TextLitKind::CurlyBracket(open) => {
                if open {
                    append_lit("{", SYMBOL_COLOR)
                } else {
                    append_lit("}", SYMBOL_COLOR)
                }
            }
            TextLitKind::Pipe => append_lit("|", SYMBOL_COLOR),
        }
    }

    pub fn cached_literal(&mut self, kind: TextLitKind) -> DrawCallId {
        if let Some(cache) = self.text_lit_drawers.get(&kind) {
            *cache
        } else {
            let lit = self.append_literal(kind);
            self.text_lit_drawers.insert(kind, lit);
            lit
        }
    }

    pub fn id_literal(&mut self, kind: TextLitKind, id: DefId) -> DrawCallId {
        let call = self.append_literal(kind);
        self.assoc_def_id(call, id);
        call
    }

    pub fn space(&mut self) -> DrawCallId {
        self.cached_literal(TextLitKind::Space)
    }

    pub fn space_width(&mut self) -> f32 {
        let id = self.space();
        self.size(id).x
    }

    pub fn noop(&mut self) -> DrawCallId {
        if let Some(id) = self.noop_drawer {
            id
        } else {
            let id = self.append(DrawCall::default());
            self.noop_drawer = Some(id);
            id
        }
    }

    pub fn append_text(&mut self, galley: Arc<Galley>, color: Color32) -> DrawCallId {
        let size = galley.size();
        self.append(DrawCall {
            kind: DrawCallKind::Text(galley, color),
            size,
        })
    }

    pub fn append_alias(&mut self, alias: &str, defs: &[DefId]) -> DrawCallId {
        let text = self.append_str(&alias);
        let size = self.size(text);
        self.append(DrawCall {
            kind: DrawCallKind::Alias(text, defs.into()),
            size,
        })
    }

    pub fn append_str(&mut self, text: &str) -> DrawCallId {
        self.append_text(text_literal(self.ctx, text), Color32::BLACK)
    }

    pub fn append_inline(&mut self, elements: Box<[RelativeDrawCallId]>, size: Vec2) -> DrawCallId {
        // let mut iter = elements
        //     .iter()
        //     .filter_map(|call| self.def_map.get(call.id).copied());
        // let id = iter.next();
        // if id.is_some() && iter.next().is_some() {
        //     println!("Inline call with multiple defs");
        // }
        self.append(DrawCall {
            kind: DrawCallKind::Inline(elements),
            size,
        })
    }

    pub fn append_spaced(&mut self, call_id: DrawCallId, margin: Margin) -> DrawCallId {
        let size = self.size(call_id) + margin.sum();
        self.append_inline(
            Box::from([RelativeDrawCallId::new(call_id, margin.left_top())]),
            size,
        )
    }

    pub fn indent(&mut self, call_id: DrawCallId) -> DrawCallId {
        let indent = self.space_width(); // * 2f32;
        self.append_spaced(
            call_id,
            Margin {
                left: indent,
                ..Default::default()
            },
        )
    }

    pub fn append_horizontal(&mut self, children: &[DrawCallId], align_bottom: bool) -> DrawCallId {
        let max_size = self.max_size(children.iter().copied());
        let mut reserved = 0f32;
        let children = Box::from_iter(children.iter().map(|id| {
            let size = self.size(*id);
            let offset = vec2(
                reserved,
                if align_bottom {
                    max_size.y - size.y
                } else {
                    0f32
                },
            );
            reserved += size.x;
            (offset, *id).into()
        }));
        self.append_inline(children, vec2(reserved, max_size.y))
    }

    pub fn append_sequential(
        &mut self,
        children: &[DrawCallId],
        align_right: bool,
        state: &State,
    ) -> DrawCallId {
        let max_size = self.max_size(children.iter().cloned());
        let mut reserved = 0f32;
        let children = Box::from_iter(children.iter().cloned().map(|mut id| {
            // make space for usage indicators
            let (assignments, usages) =
                self.find_usages(RelativeDrawCallId::root(id), &state.liveliness);
            let (in_count, out_count) = (usages.len(), assignments.len());
            if in_count > 0 || out_count > 0 {
                let offset = |count| {
                    (count > 0)
                        .then_some((count + 1) as f32 * Self::LINE_SEP)
                        .unwrap_or(0f32)
                }; // TODO: move this calc somewhere
                id = self.append_spaced(
                    id,
                    Margin {
                        top: offset(in_count),
                        bottom: offset(out_count),
                        ..Default::default()
                    },
                );
            }

            let call = RelativeDrawCallId::new(
                id,
                vec2(
                    align_right
                        .then_some(max_size.x - self.size(id).x)
                        .unwrap_or(0f32),
                    reserved,
                ),
            );
            reserved += self.size(id).y;
            call
        }));
        self.append(DrawCall {
            kind: DrawCallKind::Sequential(children),
            size: vec2(max_size.x, reserved),
        })
    }

    pub fn append_linear_control_flow(
        &mut self,
        child_id: DrawCallId,
        from_def: DefId,
        scope: Option<DefId>,
        state: &State,
    ) -> DrawCallId {
        let sequence = self.sections(child_id, from_def, state);
        let lane_mask = scope
            .map(|owner| state.liveliness.lanes_for_owner(owner))
            .unwrap_or_else(|| Liveliness::ZERO.inverted());
        let max_live_per_section = sequence
            .iter(Pos2::ZERO, Vec2::ZERO)
            .fold(0, |acc, (_, from, to, ..)| {
                acc.max(from.and(&to).and(&lane_mask).live_count())
            });
        let offset = Vec2::RIGHT * max_live_per_section as f32 * Self::LINE_SEP;
        let call = RelativeDrawCallId::new(child_id, offset);
        let size = self.size(child_id) + offset + Vec2::RIGHT * Self::LINE_SEP;
        self.append(DrawCall {
            kind: DrawCallKind::ControlFlow(sequence, call, scope),
            size,
        })
    }

    pub fn append_branched(
        &mut self,
        branches: &[(DrawCallId, DefId)],
        span: DefSpan,
        full_cf_defer: bool,
        state: &State,
    ) -> DrawCallId {
        let (mut max_live_entry, mut max_live_exit) = (
            state.liveliness.count_live_at(span.from),
            state.liveliness.count_live_at(span.to),
        );
        if max_live_entry > 0 {
            max_live_entry += 1;
        }
        if max_live_exit > 0 {
            max_live_exit += 1;
        }

        let max_height = self.max_size(branches.iter().map(|(id, _)| *id)).y;
        let y_offset = max_live_entry as f32 * Self::LINE_SEP;
        let y_offset_exit = max_live_exit as f32 * Self::LINE_SEP;
        let mut cursor = 0f32;
        let branches = Box::from_iter(branches.iter().map(|(branch_id, from_def)| {
            let branch_size = vec2(self.size(*branch_id).x, max_height);
            self.set_size(*branch_id, branch_size);
            let mut branch_id = self.append_boxed(
                *branch_id,
                Margin::ZERO,
                Rounding::same(10f32),
                Color32::from_black_alpha(10),
            );
            branch_id = self.append_linear_control_flow(branch_id, *from_def, None, state);
            let offset = vec2(cursor, y_offset);
            cursor += self.size(branch_id).x + Self::LINE_SEP;
            RelativeDrawCallId::new(branch_id, offset)
        }));

        let height = y_offset + max_height + y_offset_exit;
        self.append(DrawCall {
            kind: DrawCallKind::Branch(branches, span, full_cf_defer),
            size: vec2(cursor, height),
        })
    }

    pub fn append_rect(&mut self, color: Color32, rounding: Rounding, size: Vec2) -> DrawCallId {
        self.append(DrawCall {
            kind: DrawCallKind::Rect(color, rounding),
            size,
        })
    }

    pub fn append_boxed(
        &mut self,
        call: DrawCallId,
        margin: Margin,
        rounding: Rounding,
        color: Color32,
    ) -> DrawCallId {
        let size = self.size(call) + margin.sum();
        let rect_id = self.append_rect(color, rounding, size);
        self.append_inline(
            Box::from([
                RelativeDrawCallId::root(rect_id),
                RelativeDrawCallId::new(call, margin.left_top()),
            ]),
            size,
        )
    }

    pub fn append_braced(
        &mut self,
        child_id: DrawCallId,
        bracket_type: BracketType,
        color: Color32,
    ) -> DrawCallId {
        if self.is_complex(child_id) {
            const BRACKET_WIDTH: f32 = 5f32;
            let size =
                self.size(child_id).max(vec2(5f32, 16f32)) + vec2(BRACKET_WIDTH * 2f32, 0f32);
            let bracket_id = self.append(DrawCall {
                kind: DrawCallKind::Bracketed(bracket_type, color, BRACKET_WIDTH),
                size,
            });
            self.append_inline(
                [
                    RelativeDrawCallId::root(bracket_id),
                    RelativeDrawCallId::new(child_id, Vec2::RIGHT * BRACKET_WIDTH),
                ]
                .into(),
                size,
            )
        } else {
            let (open, close) = match bracket_type {
                BracketType::Round => (
                    TextLitKind::RoundBracket(true),
                    TextLitKind::RoundBracket(false),
                ),
                BracketType::Square => (
                    TextLitKind::SquareBracket(true),
                    TextLitKind::SquareBracket(false),
                ),
                BracketType::Pipe => (TextLitKind::Pipe, TextLitKind::Pipe),
                BracketType::Curly => (
                    TextLitKind::CurlyBracket(true),
                    TextLitKind::CurlyBracket(false),
                ),
            };
            let (open, close) = (self.cached_literal(open), self.cached_literal(close));
            self.append_horizontal(&[open, child_id, close], false)
        }
    }

    pub fn append_closure(
        &mut self,
        call_id: DrawCallId,
        outer_id: DefId,
        inner_id: DefId,
        state: &State,
    ) -> DrawCallId {
        let call_id = self.append_linear_control_flow(call_id, inner_id, Some(inner_id), state);
        let size = self.size(call_id);
        self.append(DrawCall {
            kind: DrawCallKind::Closure(call_id, outer_id),
            size,
        })
    }

    pub fn is_complex(&self, call_id: DrawCallId) -> bool {
        self.call_complexity.get(call_id).copied().unwrap_or(false)
    }

    fn find_usages(
        &self,
        call: RelativeDrawCallId,
        liveliness: &DefLivelinessInfo,
    ) -> (
        Vec<(LaneIndex, RelativeDrawCallId, DefId, bool)>,
        Vec<(LaneIndex, RelativeDrawCallId, DefId, UsageKind, bool)>,
    ) {
        let (mut assignments, mut usages): (Vec<_>, Vec<_>) = Default::default();
        let mut visit_def = |child: RelativeDrawCallId, def_id: DefId| {
            for lane in liveliness.assignments_for(def_id).unwrap_or_default() {
                if liveliness.is_lane_active(*lane) {
                    // only show assignments for lanes that are actually used..
                    assignments.push((*lane, child.offset(call.offset), def_id, false));
                }
            }
            for (lane, kind) in liveliness.usages_for(def_id).unwrap_or_default() {
                usages.push((*lane, child.offset(call.offset), def_id, *kind, false));
            }
        };

        self.walk_children(call.id, &mut |child| {
            if let Some((def_id, false)) = self.def_map.get(child.id) {
                visit_def(child, *def_id);
            }
            match &self.buffer[child.id].kind {
                DrawCallKind::Alias(_, defs) => {
                    for def in defs.iter() {
                        visit_def(child, *def);
                    }
                    TreeWalkerState::<()>::Continue
                }
                DrawCallKind::Closure(..)
                | DrawCallKind::Branch(..)
                | DrawCallKind::Sequential(..) => TreeWalkerState::<()>::Continue,
                _ => TreeWalkerState::DescendToChildren,
            }
        });
        (assignments, usages)
    }

    pub fn active_count(&self, call: DrawCallId, liveliness: &DefLivelinessInfo) -> usize {
        let mut count = 0;
        self.walk_children(call, &mut |child| {
            count += self
                .def_map
                .get(child.id)
                .map(|(def, _)| liveliness.active_count_for(*def))
                .unwrap_or(0);
            match &self.buffer[child.id].kind {
                DrawCallKind::Closure(..) | DrawCallKind::Branch(..) => {
                    TreeWalkerState::<()>::Continue
                }
                _ => TreeWalkerState::DescendToChildren,
            }
        });
        count
    }

    fn sections(&self, call_id: DrawCallId, from_def: DefId, state: &State) -> CFSections {
        let mut sections = vec![];

        let mut stack = vec![RelativeDrawCallId::root(call_id)];
        while let Some(top_call) = stack.pop() {
            let mut push_section = |kind: CFKind, liveliness: Liveliness| {
                sections.push((
                    top_call.offset.y + self.size(top_call.id).y,
                    liveliness,
                    kind,
                ));
            };
            if self.is_complex(top_call.id) {
                match &self.buffer[top_call.id].kind {
                    DrawCallKind::Branch(branches, span, full_cf_defer) => {
                        push_section(
                            CFKind::Branch(
                                Box::from_iter(branches.iter().filter_map(|branch| {
                                    self.find_def_span(branch.id, &state.order, &state.first_def)
                                        .map(|span| (branch.offset(top_call.offset), span))
                                })),
                                *full_cf_defer,
                            ),
                            state.liveliness.liveliness_at(span.to),
                        );
                    }
                    DrawCallKind::Closure(_, def_id) => {
                        let (assignments, captures) = self.find_usages(top_call, &state.liveliness);
                        assert!(assignments.len() == 0);
                        push_section(
                            CFKind::Closure(captures),
                            state.liveliness.liveliness_at(*def_id),
                        )
                    }
                    DrawCallKind::ControlFlow(inner, child_call, owner) => {
                        let handled = owner
                            .map(|owner| state.liveliness.lanes_for_owner(owner))
                            .unwrap_or_else(|| Liveliness::ZERO);

                        for (kind, _, liveliness, _, to) in
                            inner.iter(top_call.offset.to_pos2(), child_call.offset)
                        {
                            sections.push((
                                to.y,
                                liveliness.and(&handled.inverted()),
                                kind.filter(handled),
                            ));
                        }
                    }
                    _ => {
                        let mut push = |child: RelativeDrawCallId| {
                            stack.push(child.offset(top_call.offset));
                        };
                        match &self.buffer[top_call.id].kind {
                            DrawCallKind::Inline(children) => {
                                assert!(
                                    children
                                        .iter()
                                        .filter(|child| self.is_complex(child.id))
                                        .count()
                                        < 2, "In a complex `Inline` DrawCall there may only be 1 complex sub-call."
                                );
                                if let Some(child) =
                                    children.iter().find(|child| self.is_complex(child.id))
                                {
                                    push(*child);
                                }
                            }
                            DrawCallKind::Sequential(children) => {
                                for child in children.iter().rev() {
                                    push(*child);
                                }
                            }
                            _ => (),
                        }
                    }
                }
            } else {
                if let Some(span) = self.find_def_span(top_call.id, &state.order, &state.first_def)
                {
                    let (assignments, usages) = self.find_usages(top_call, &state.liveliness);
                    push_section(
                        CFKind::Line(assignments, usages),
                        state.liveliness.liveliness_at(span.to),
                    );
                }
            }
        }

        let end_y = self.size(call_id).y;
        if let Some((last_end_y, liveliness, _)) = sections.last() {
            if *last_end_y != end_y {
                sections.push((end_y, *liveliness, CFKind::Line(vec![], vec![])))
            }
        }

        CFSections {
            liveliness: state.liveliness.liveliness_at(from_def),
            sections: sections.into_boxed_slice(),
        }
    }

    pub fn max_size(&self, items: impl IntoIterator<Item = DrawCallId>) -> Vec2 {
        items
            .into_iter()
            .fold(Vec2::ZERO, |acc, id| acc.max(self.size(id).ceil()))
    }

    pub fn size(&self, call_id: DrawCallId) -> Vec2 {
        self.buffer[call_id].size
    }

    pub fn set_size(&mut self, call_id: DrawCallId, size: Vec2) {
        self.buffer[call_id].size = size;
    }

    fn walk_children<T>(
        &self,
        call_id: DrawCallId,
        func: &mut impl FnMut(RelativeDrawCallId) -> TreeWalkerState<T>,
    ) -> Option<T> {
        let mut stack = vec![RelativeDrawCallId::root(call_id)];
        while let Some(top_call) = stack.pop() {
            let mut push = |children: &[RelativeDrawCallId]| {
                stack.extend(
                    children
                        .iter()
                        .rev()
                        .map(|child_call| child_call.offset(top_call.offset)),
                );
            };
            match func(top_call) {
                TreeWalkerState::Stop => return None,
                TreeWalkerState::Return(val) => return Some(val),
                TreeWalkerState::DescendToChildren => match &self.buffer[top_call.id].kind {
                    DrawCallKind::Alias(id, ..) | DrawCallKind::Closure(id, ..) => {
                        push(&[RelativeDrawCallId::root(*id)])
                    }
                    DrawCallKind::ControlFlow(_, id, _) => push(&[*id]),
                    DrawCallKind::Branch(children, ..)
                    | DrawCallKind::Inline(children)
                    | DrawCallKind::Sequential(children) => push(&children),
                    DrawCallKind::Bracketed(..)
                    | DrawCallKind::Text(..)
                    | DrawCallKind::Rect(..)
                    | DrawCallKind::Noop => (),
                },
                TreeWalkerState::Continue => (),
            }
        }
        None
    }

    fn find_def_span(
        &self,
        call_id: DrawCallId,
        order: &ArenaMap<DefId, u32>,
        first_def: &ArenaMap<DefId, DefId>,
    ) -> Option<DefSpan> {
        if let Some((def, false)) = self.def_map.get(call_id).copied() {
            let from = first_def.get(def).copied().unwrap_or(def);
            return Some(DefSpan { from, to: def });
        }

        self.walk_children(call_id, &mut |call| match &self.buffer[call.id].kind {
            DrawCallKind::Sequential(sequence) => {
                let to_span = |call: Option<&RelativeDrawCallId>| {
                    call.and_then(|call| self.find_def_span(call.id, order, first_def))
                };
                match (to_span(sequence.first()), to_span(sequence.last())) {
                    (Some(first_span), Some(last_span)) => TreeWalkerState::Return(DefSpan {
                        from: first_span.from,
                        to: last_span.to,
                    }),
                    (Some(first_span), None) => TreeWalkerState::Return(first_span),
                    (None, Some(last_span)) => TreeWalkerState::Return(last_span),
                    _ => TreeWalkerState::Stop,
                }
            }
            DrawCallKind::Branch(_, span, _) => TreeWalkerState::Return(*span),
            DrawCallKind::Inline(children) => children
                .iter()
                .filter_map(|call| self.find_def_span(call.id, order, first_def))
                .fold(None, |accu: Option<DefSpan>, span| {
                    if let Some(accu) = accu {
                        Some(accu.unite(&span, order))
                    } else {
                        Some(span)
                    }
                })
                .map(|span| TreeWalkerState::Return(span))
                .unwrap_or(TreeWalkerState::Stop),
            DrawCallKind::Closure(_, id) => TreeWalkerState::Return(DefSpan { from: *id, to: *id }),
            _ => TreeWalkerState::DescendToChildren,
        })
    }

    fn draw_linear(
        &self,
        painter: &Painter,
        sequence: &CFSections,
        scope: Option<DefId>,
        rect: Rect,
        content_offset: Vec2,
        state: &State,
    ) {
        let handled_lanes = scope
            .map(|scope| state.liveliness.lanes_for_owner(scope))
            .unwrap_or_else(|| Liveliness::ZERO.inverted());

        let lane_offset = |index: u32| Self::LINE_SEP * index as f32;
        let lane_stroke = |lane: LaneIndex, liveliness: &Liveliness| -> Stroke {
            state.liveliness.stroke(liveliness.is_locked(lane), lane)
        };

        let origin = rect.left_top();

        let draw_call_rect = |call: RelativeDrawCallId| -> Rect {
            Rect::from_min_size(call.offset.to_pos2(), self.size(call.id))
        };

        for (kind, live_entry, live_exit, from, to) in sequence.iter(origin, content_offset) {
            let (live_entry, live_exit) =
                (live_entry, live_exit).map(|liveliness| liveliness.and(&handled_lanes));

            let join_pos = |lane: LaneIndex, index: usize, kind: UsageKind| -> Pos2 {
                let index = match kind {
                    UsageKind::Move(_) => index,
                    _ => index + 1,
                };
                snap_pos(
                    pos2(origin.x, from.y)
                        + Vec2::DOWN * (index as f32 * Self::LINE_SEP)
                        + Vec2::RIGHT * lane_offset(live_entry.index_for(lane)),
                )
            };

            if !matches!(kind, CFKind::Branch(.., true)) {
                for lane in live_entry.iter_live() {
                    let stroke = lane_stroke(lane, &live_entry);
                    let (lane_index_entry, lane_index_exit) =
                        (&live_entry, &live_exit).map(|live| live.index_for(lane));
                    let lane_changed = lane_index_entry != lane_index_exit;

                    let mut entry_pos = snap_pos(
                        pos2(origin.x, from.y) + Vec2::RIGHT * lane_offset(lane_index_entry),
                    );
                    let exit_pos =
                        snap_pos(pos2(origin.x, to.y) + Vec2::RIGHT * lane_offset(lane_index_exit));

                    let moved = if let CFKind::Line(_, usages) | CFKind::Closure(usages) = &kind {
                        if let Some((last_index, kind)) = usages.iter().enumerate().rev().find_map(
                            |(index, (usage_lane, .., kind, handled))| {
                                (*usage_lane == lane && !*handled).then_some((index, *kind))
                            },
                        ) {
                            let pos = join_pos(lane, last_index, kind);
                            painter.line_segment([entry_pos, pos], stroke); // extend straight line until last usage
                            entry_pos = pos;
                        }
                        usages.iter().any(|(usage_lane, .., kind, handled)| {
                            *usage_lane == lane
                                && matches!(kind, UsageKind::Move(false))
                                && !*handled
                        })
                    } else {
                        false
                    };

                    let live_exit = live_exit.is_live(lane);
                    if live_exit && !moved {
                        if lane_changed {
                            let mid_y = snap((entry_pos.y + exit_pos.y) * 0.5f32);
                            painter.add(bezier4(
                                entry_pos,
                                pos2(entry_pos.x, mid_y),
                                pos2(exit_pos.x, mid_y),
                                exit_pos + Vec2::DOWN, // not sure why, but bezier-curves seem to stop 1px short..
                                stroke,
                            ));
                        } else {
                            painter.line_segment([entry_pos, exit_pos], stroke);
                        }
                    }
                    // if !live_exit && !moved && !assigned {
                    //     draw_cross(painter, entry_pos, Self::LINE_WIDTH * 2f32, stroke);
                    // }
                }
            }

            if let CFKind::Branch(branches, _) = &kind {
                let (count_entry, count_exit) = (live_entry, live_exit).map(|l| l.live_count() + 1);

                // draw active lanes for entry/exit
                for (index, lane) in live_entry.iter_live().enumerate() {
                    let from_y = branches.iter().fold(0f32, |init, (call, _)| {
                        draw_call_rect(*call).top().max(init)
                    });

                    draw_spread(
                        painter,
                        snap_pos(
                            pos2(origin.x, from.y) + Vec2::RIGHT * lane_offset(index as u32 + 1),
                        ),
                        snap(from_y + Vec2::DOWN.y),
                        branches.iter().filter_map(|(x, span)| {
                            let liveliness = state.liveliness.liveliness_at(span.from);
                            liveliness.is_live(lane).then_some({
                                let lane_index = liveliness.index_for(lane);
                                snap(draw_call_rect(*x).left() + lane_offset(lane_index))
                            })
                        }),
                        from.y + lane_offset(count_entry - index as u32 - 1),
                        lane_stroke(lane, &live_entry),
                    );
                }
                for (index, lane) in live_exit.iter_live().enumerate() {
                    let to_y = branches.iter().fold(0f32, |init, (call, _)| {
                        draw_call_rect(*call).bottom().max(init)
                    });
                    draw_spread(
                        painter,
                        snap_pos(
                            pos2(origin.x, to.y) + Vec2::RIGHT * lane_offset(index as u32 + 1),
                        ),
                        snap(to_y),
                        branches.iter().filter_map(|(x, span)| {
                            let liveliness = state.liveliness.liveliness_at(span.to);
                            liveliness.is_live(lane).then_some({
                                let lane_index = liveliness.index_for(lane);
                                snap(draw_call_rect(*x).left() + lane_offset(lane_index))
                            })
                        }),
                        to.y - lane_offset(count_exit - index as u32 - 1),
                        lane_stroke(lane, &live_exit),
                    );
                }
            }

            if let CFKind::Line(_, usages) | CFKind::Closure(usages) = &kind {
                for (index, (lane, call, _, usage_kind, handled)) in
                    usages.iter().cloned().enumerate()
                {
                    if !handled_lanes.is_live(lane) || handled {
                        continue;
                    }

                    let stroke = lane_stroke(lane, &live_entry);

                    let usage_rect = draw_call_rect(call);
                    let usage_pos = snap_pos(
                        matches!(kind, CFKind::Closure(..))
                            .then_some(usage_rect.left_top() + Vec2::RIGHT * Self::LINE_SEP)
                            .unwrap_or(usage_rect.center_top()),
                    );
                    let join_pos = join_pos(lane, index, usage_kind);

                    match usage_kind {
                        UsageKind::Move(partial) => {
                            let line_y = join_pos.y + Self::LINE_SEP;
                            draw_move(
                                painter,
                                join_pos,
                                line_y,
                                usage_pos,
                                Self::LINE_SEP * 0.8f32,
                                partial,
                                stroke,
                            );
                        }
                        UsageKind::Copy => {
                            draw_copy(painter, join_pos, usage_pos, stroke);
                        }
                        UsageKind::Reference(mutable) => {
                            let ref_stroke = state.liveliness.raw_stroke(lane, false, mutable);
                            draw_ref(
                                painter,
                                join_pos,
                                Self::LINE_SEP * 0.8f32,
                                usage_pos,
                                ref_stroke,
                            );
                        }
                        UsageKind::Deref => {
                            painter.circle_filled(join_pos, Self::LINE_SEP * 0.5f32, stroke.color);
                            draw_copy(
                                painter,
                                join_pos,
                                usage_pos,
                                state.liveliness.stroke(live_entry.is_locked(lane), lane),
                            );
                        }
                    }
                }
            }
            if let CFKind::Line(assignments, _) = &kind {
                for (index, (lane, call, .., handled)) in assignments.iter().cloned().enumerate() {
                    if !handled_lanes.is_live(lane) || handled {
                        continue;
                    }

                    let stroke = lane_stroke(lane, &live_exit);
                    let assign_pos = snap_pos(draw_call_rect(call).center_bottom());
                    let join_pos = snap_pos(
                        pos2(origin.x, to.y) + Vec2::RIGHT * lane_offset(live_exit.index_for(lane)),
                    );
                    let line_y = assign_pos.y + (index + 1) as f32 * Self::LINE_SEP;
                    draw_arc(painter, join_pos, line_y, assign_pos, stroke);
                }
            }
        }
    }

    pub fn draw(
        &self,
        painter: &Painter,
        rect: Rect,
        id: DrawCallId,
        cursor: Pos2,
        state: &State,
        conflicts: &ArenaMap<DefId, Vec<Conflict>>,
        selectable: &DefSet,
    ) -> Selection {
        let mut selected = Selection::default();
        let mut def_rects = ArenaMap::default();

        let mut stack = vec![(RelativeDrawCallId::root(id), 0u32, None)];
        while let Some((top, depth, mut highlight)) = stack.pop() {
            let kind = &self.buffer[top.id].kind;
            let rect = Rect::from_min_size(rect.left_top() + top.offset, self.size(top.id));

            // visualized draw calls
            // painter.rect_filled(
            //     rect,
            //     Rounding::ZERO,
            //     Hsva::new(
            //         (top.id.into_raw().into_u32() * 10 + depth) as f32 * 0.03f32 % 1f32,
            //         0.8f32,
            //         0.9f32,
            //         0.6f32,
            //     ),
            // );

            if let Some((def, _)) = self.def_map.get(top.id).copied() {
                def_rects.insert(def, rect);

                if state.selected.contains(&def) {
                    painter.rect_filled(
                        rect,
                        Rounding::same(2f32),
                        Color32::from_rgba_unmultiplied(255, 255, 100, 100),
                    );
                }

                if let Some(lane) = state.liveliness.lane_for_def(def) {
                    highlight = Some(state.liveliness.color(lane));
                }

                if selectable[def] && rect.contains(cursor) {
                    selected.update(def, depth);
                    painter.rect_stroke(rect, Rounding::ZERO, Stroke::new(0.2f32, Color32::BLACK));
                }
            }

            // draw
            match kind {
                DrawCallKind::Text(galley, color) => painter.galley_with_color(
                    rect.left_top(),
                    galley.clone(),
                    highlight.unwrap_or(*color),
                ),
                DrawCallKind::Bracketed(kind, color, width) => {
                    kind.shape(&rect, *width, highlight.unwrap_or(*color))
                        .map(|shape| painter.add(shape));
                }
                DrawCallKind::Rect(color, rounding) => {
                    painter.rect_filled(rect, *rounding, *color);
                }
                DrawCallKind::ControlFlow(sections, child_call, scope) => {
                    self.draw_linear(painter, &sections, *scope, rect, child_call.offset, state);
                }
                _ => (),
            }

            // draw children
            match &self.buffer[top.id].kind {
                DrawCallKind::Closure(id, _) => {
                    if let Some(highlight) = highlight {
                        painter.rect_stroke(
                            rect.shrink(1f32),
                            Rounding::ZERO,
                            Stroke::new(Self::LINE_WIDTH, highlight),
                        );
                    }
                    stack.push((RelativeDrawCallId::new(*id, top.offset), depth + 1, None));
                }
                DrawCallKind::Alias(alias, defs) => stack.push((
                    RelativeDrawCallId::new(*alias, top.offset),
                    depth + 1,
                    defs.iter()
                        .find_map(|def| state.liveliness.lane_for_def(*def))
                        .map(|lane| state.liveliness.color(lane))
                        .or(highlight),
                )),
                DrawCallKind::ControlFlow(_, child, _) => {
                    stack.push((child.offset(top.offset), depth + 1, highlight))
                }
                DrawCallKind::Branch(children, ..)
                | DrawCallKind::Inline(children)
                | DrawCallKind::Sequential(children) => {
                    stack.extend(
                        children
                            .iter()
                            .rev()
                            .map(|child| (child.offset(top.offset), depth + 1, highlight)),
                    );
                }
                _ => (),
            }
        }

        let error_stroke = Stroke::new(1f32, Color32::RED);

        for (from, conflicts) in conflicts.iter() {
            if let Some(usage_rect) = def_rects.get(from) {
                painter.rect_stroke(
                    usage_rect.expand(1.5f32),
                    Rounding::same(5f32),
                    error_stroke,
                );

                let hovered = usage_rect.contains(cursor);
                if hovered || state.liveliness.active_defs.contains_idx(from) {
                    for conflict in conflicts {
                        for target_rect in
                            conflict.targets.iter().filter_map(|id| def_rects.get(*id))
                        {
                            painter.rect_stroke(
                                target_rect.expand(2.5f32),
                                Rounding::same(5f32),
                                error_stroke,
                            );
                        }
                    }
                }
                if hovered {
                    painter.debug_text(
                        cursor,
                        Align2::LEFT_BOTTOM,
                        Color32::WHITE,
                        conflicts.iter().map(|conflict| conflict.kind).join("\n"),
                    );
                }
            }
        }

        selected
    }
}

fn snap(x: f32) -> f32 {
    x.floor() + 0.5f32
}

fn snap_pos(pos: Pos2) -> Pos2 {
    pos2(snap(pos.x), snap(pos.y))
}

fn bezier3(a: Pos2, b: Pos2, c: Pos2, stroke: Stroke) -> Shape {
    Shape::QuadraticBezier(QuadraticBezierShape::from_points_stroke(
        [a, b, c],
        false,
        Color32::TRANSPARENT,
        stroke,
    ))
}

fn bezier4(a: Pos2, b: Pos2, c: Pos2, d: Pos2, stroke: Stroke) -> Shape {
    Shape::CubicBezier(CubicBezierShape::from_points_stroke(
        [a, b, c, d],
        false,
        Color32::TRANSPARENT,
        stroke,
    ))
}

fn draw_spread(
    painter: &Painter,
    join: Pos2,
    branches_y: f32,
    branches: impl Iterator<Item = f32>,
    line_height: f32,
    stroke: Stroke,
) {
    let join_arc_radius = (join.y - line_height).abs();
    let branch_arc_radius = (branches_y - line_height).abs();
    let line_start = pos2(join.x + join_arc_radius, line_height);

    let mut end_x = join.x + join_arc_radius;
    for (index, branch_x) in branches.enumerate() {
        if index == 0 {
            painter.add(bezier3(join, pos2(join.x, line_height), line_start, stroke));
        }
        end_x = end_x.max(branch_x - branch_arc_radius);
        painter.add(bezier3(
            pos2(branch_x, branches_y),
            pos2(branch_x, line_height),
            pos2(
                (branch_x - branch_arc_radius).max(line_start.x),
                line_height,
            ),
            stroke,
        ));
    }
    if end_x > line_start.x {
        painter.line_segment([line_start, pos2(end_x, line_height)], stroke);
    }
}

fn draw_arc(painter: &Painter, join: Pos2, line_height: f32, end: Pos2, stroke: Stroke) {
    let join_arc_radius = (join.y - line_height).abs();
    let branch_arc_radius = (end.y - line_height).abs();
    let line_start = pos2(join.x + join_arc_radius, line_height);
    painter.add(bezier3(join, pos2(join.x, line_height), line_start, stroke));
    let arc_end = pos2((end.x - branch_arc_radius).max(line_start.x), line_height);
    painter.add(bezier3(end, pos2(end.x, line_height), arc_end, stroke));
    let end_x = (join.x + join_arc_radius).max(end.x - branch_arc_radius);
    if end_x > line_start.x {
        painter.line_segment([line_start, pos2(end_x, line_height)], stroke);
    }
}

fn draw_copy(painter: &Painter, join: Pos2, usage: Pos2, stroke: Stroke) {
    let corner = pos2(usage.x, join.y);
    painter.line_segment([join, corner + Vec2::RIGHT * stroke.width * 0.5f32], stroke);
    painter.line_segment([corner, usage], stroke);
}

fn draw_ref(painter: &Painter, join: Pos2, size: f32, usage: Pos2, stroke: Stroke) {
    let up = Vec2::UP * size * 0.75f32;
    let right = Vec2::RIGHT * size;
    painter.add(Shape::Path(PathShape::convex_polygon(
        vec![join, join + right + up, join + right - up],
        stroke.color,
        Stroke::NONE,
    )));

    draw_copy(painter, join, usage, stroke);
}

fn draw_move(
    painter: &Painter,
    join_pos: Pos2,
    line_y: f32,
    move_pos: Pos2,
    size: f32,
    partial: bool,
    stroke: Stroke,
) {
    let up = Vec2::UP * size;
    let right = Vec2::RIGHT * size * 0.75f32;

    draw_arc(painter, join_pos, line_y, move_pos, stroke);

    if !partial {
        let move_pos = move_pos + Vec2::DOWN * size * 0.5f32;
        painter.add(Shape::Path(PathShape::convex_polygon(
            vec![move_pos, move_pos + right + up, move_pos - right + up],
            stroke.color,
            Stroke::NONE,
        )));
    }
}

fn draw_cross(painter: &Painter, pos: Pos2, size: f32, stroke: Stroke) {
    let right = Vec2::RIGHT * size;
    let up = Vec2::UP * size;
    painter.line_segment([pos - right + up, pos + right - up], stroke);
    painter.line_segment([pos - right - up, pos + right + up], stroke);
}

pub fn text_literal(ctx: &egui::Context, text: &str) -> Arc<Galley> {
    ctx.fonts(|fonts| {
        fonts.layout_job(LayoutJob {
            halign: Min,
            ..LayoutJob::simple_singleline(
                String::from(text),
                FontId::monospace(16.),
                Color32::TEMPORARY_COLOR,
            )
        })
    })
}

#[derive(Default)]
pub struct Selection {
    pub def_id: Option<(DefId, u32)>,
}
impl Selection {
    fn update(&mut self, selected_id: DefId, depth: u32) {
        if match self.def_id {
            None => true,
            Some((_, selection_depth)) if selection_depth < depth => true,
            _ => false,
        } {
            self.def_id = Some((selected_id, depth));
        }
    }

    pub fn selected_thir(&self) -> Option<DefId> {
        self.def_id.map(|(thir_id, _)| thir_id)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BracketType {
    Round,
    Square,
    Pipe,
    Curly,
}

impl BracketType {
    pub fn shape(&self, rect: &Rect, width: f32, color: Color32) -> (Shape, Shape) {
        let stroke = Stroke::new(1.5f32, color);
        let offset = Vec2::RIGHT * (width - stroke.width);
        let rect = rect.shrink2(vec2(stroke.width, 0f32));
        let open = [
            rect.left_top() + offset,
            rect.left_top(),
            rect.left_bottom(),
            rect.left_bottom() + offset,
        ];
        let close = [
            rect.right_top() - offset,
            rect.right_top(),
            rect.right_bottom(),
            rect.right_bottom() - offset,
        ];
        (open, close).map(|points| match self {
            BracketType::Round => Shape::CubicBezier(CubicBezierShape::from_points_stroke(
                points,
                false,
                Color32::TRANSPARENT,
                stroke,
            )),
            BracketType::Curly | BracketType::Square => Shape::line(points.to_vec(), stroke),
            BracketType::Pipe => {
                let dir = (points[1] - points[0].to_vec2()).to_vec2() * 0.5;
                Shape::line_segment([points[0] + dir, points[3] + dir], stroke)
            }
        })
    }
}
