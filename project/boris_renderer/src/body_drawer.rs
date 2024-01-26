use std::iter;

use boris_shared::{
    ArithOp, Array, BinaryOp, CaptureBy, Def, DefId, Expr, ForLoopResugaring, MacroResugaring,
    Mutability, Pat, PathInfo, QuestionMarkResugaring, Resugaring, Statement, ThirBody,
    WhileLoopResugaring,
};
use eframe::{
    egui::Margin,
    epaint::{Color32, Rounding, Vec2},
};
use egui::vec2;
use itertools::Itertools;

use crate::drawer::{
    BracketType, DefSpan, DrawBuffer, DrawCallId, RelativeDrawCallId, State, TextLitKind,
};
struct BodyRenderer<'a> {
    body: &'a ThirBody,
    state: State,
}

impl<'a> BodyRenderer<'a> {
    fn append_args(&self, buffer: &mut DrawBuffer, args: &[DrawCallId]) -> DrawCallId {
        if args.iter().any(|arg| buffer.is_complex(*arg)) {
            buffer.append_sequential(args, false, &self.state)
        } else {
            let items = args
                .iter()
                .cloned()
                .interleave((1..args.len()).map(|_| buffer.literal(TextLitKind::Comma)))
                .collect_vec();
            buffer.append_horizontal(&items, true)
        }
    }

    fn append_bracketed(&self, buffer: &mut DrawBuffer, id: DefId, parent_id: DefId) -> DrawCallId {
        let call = self.append_def(buffer, id);
        if self.body.defs[id].precedence() < self.body.defs[parent_id].precedence() {
            buffer.append_braced(call, BracketType::Round, Color32::BLACK)
        } else {
            call
        }
    }

    fn append_split(
        &self,
        buffer: &mut DrawBuffer,
        arms: &[DrawCallId],
        span: DefSpan,
        full_cf_defer: bool,
    ) -> DrawCallId {
        buffer.append_branched(arms, span, full_cf_defer, &self.state)
    }

    fn append_binary_op(
        &self,
        buffer: &mut DrawBuffer,
        lhs: DrawCallId,
        rhs: DrawCallId,
        op: DrawCallId,
        right_to_left: bool,
    ) -> DrawCallId {
        if buffer.is_complex(lhs) || buffer.is_complex(rhs) {
            //     // if it is an assignment, evaluation order goes from right to left, otherwise left to right
            if right_to_left {
                let lhs_op_id = buffer.append_horizontal(&[lhs, op], false);
                let lhs_height = buffer.size(lhs_op_id).y;

                let size = buffer.size(rhs);
                let rect_id = buffer.append_rect(
                    Color32::from_black_alpha(10),
                    Rounding::ZERO,
                    size + Vec2::DOWN * lhs_height,
                );
                let rhs_id = buffer.append_inline(
                    [
                        RelativeDrawCallId::root(rect_id),
                        RelativeDrawCallId::root(rhs), // this is higher than the rect we allocate for this call, but thats intended in this case
                    ]
                    .into(),
                    size,
                );

                let spaced_rhs = buffer.append_spaced(
                    rhs_id,
                    Margin {
                        left: buffer.size(lhs_op_id).x,
                        ..Default::default()
                    },
                );

                buffer.append_sequential(&[spaced_rhs, lhs_op_id], false, &self.state)
            } else {
                let space = buffer.space();
                let op_rhs_id = buffer.append_horizontal(&[space, op, rhs], false);
                buffer.append_sequential(&[lhs, op_rhs_id], false, &self.state)
            }
        } else {
            buffer.append_horizontal(&[lhs, op, rhs], false)
        }
    }

    fn append_let(
        &self,
        buffer: &mut DrawBuffer,
        pat: DefId,
        type_ref: Option<&str>,
        init: Option<DefId>,
        else_branch: Option<DefId>,
    ) -> DrawCallId {
        let let_lit = buffer.literal(TextLitKind::Let);
        let lhs = if let Some(type_ref) = type_ref {
            let children = [
                let_lit,
                self.append_def(buffer, pat),
                buffer.literal(TextLitKind::Colon),
                buffer.space(),
                buffer.append_str(type_ref),
            ];
            buffer.append_horizontal(&children, true)
        } else {
            let children = [let_lit, self.append_def(buffer, pat)];
            buffer.append_horizontal(&children, true)
        };
        let drawer = if let Some(init) = init {
            let rhs = self.append_def(buffer, init);
            let op = buffer.literal(TextLitKind::BinaryOp(BinaryOp::Assignment { op: None }));
            self.append_binary_op(buffer, lhs, rhs, op, true)
        } else {
            lhs
        };
        if let Some(else_def) = else_branch {
            let branches = [self.append_def(buffer, else_def)];
            let span = DefSpan {
                from: pat,
                to: else_def,
            };
            let else_id = self.append_split(buffer, &branches, span, false);
            buffer.append_sequential(&[drawer, else_id], false, &self.state)
        } else {
            drawer
        }
    }

    fn append_statement(&self, buffer: &mut DrawBuffer, statement: &Statement) -> DrawCallId {
        let id = match statement {
            Statement::Let {
                pat,
                type_ref,
                initializer,
                else_branch,
            } => self.append_let(
                buffer,
                *pat,
                type_ref.as_deref(),
                *initializer,
                *else_branch,
            ),
            Statement::Expr { expr } => self.append_def(buffer, *expr),
        };

        if buffer.is_complex(id) {
            id
        } else {
            let children = [id, buffer.literal(TextLitKind::Semi)];
            let id = buffer.append_horizontal(&children, false);

            const space: f32 = 1f32;
            buffer.append_spaced(
                id,
                Margin {
                    top: space,
                    bottom: space,
                    ..Default::default()
                },
            )
        }
    }

    fn append_ref(&self, buffer: &mut DrawBuffer, id: DefId, mutability: Mutability) -> DrawCallId {
        let children = [
            buffer.literal(TextLitKind::Ref(mutability)),
            self.append_def(buffer, id),
        ];
        buffer.append_horizontal(&children, false)
    }

    fn append_tuple(
        &self,
        buffer: &mut DrawBuffer,
        defs: &[DefId],
        dots: Option<usize>,
    ) -> DrawCallId {
        let dots_id = buffer.literal(TextLitKind::Dots);
        let args = Box::from_iter(defs.iter().map(|id| self.append_def(buffer, *id)));
        let args = dots
            .map(|i| {
                Box::from_iter(
                    args.iter()
                        .cloned()
                        .take(i)
                        .chain(iter::once(dots_id))
                        .chain(args.iter().skip(i).cloned()),
                )
            })
            .unwrap_or(args);
        let id = self.append_args(buffer, &args);
        buffer.append_braced(id, BracketType::Round, Color32::BLACK)
    }

    fn append_labelled(
        &self,
        buffer: &mut DrawBuffer,
        kind: TextLitKind,
        label: Option<&str>,
    ) -> DrawCallId {
        let lit = buffer.literal(kind);
        if let Some(label) = label {
            let children = [
                lit,
                buffer.space(),
                // buffer.literal(TextLitKind::Tick),
                // buffer.space(),
                buffer.append_str(label),
            ];
            buffer.append_horizontal(&children, false)
        } else {
            lit
        }
    }

    fn append_expr(&self, buffer: &mut DrawBuffer, expr: &Expr, id: DefId) -> DrawCallId {
        match expr {
            Expr::Path(info) => match info {
                PathInfo::Binding(id) => buffer.append_str(&self.body.bindings[*id].name()),
                PathInfo::Path(path) => buffer.append_str(&path),
            },
            Expr::Literal(lit) => buffer.append_str(&lit),
            Expr::Block {
                statements, tail, ..
            } => {
                let mut ids = statements
                    .iter()
                    .map(|s| self.append_statement(buffer, s))
                    .collect_vec();
                ids.extend(tail.iter().map(|id| self.append_def(buffer, *id)));
                let block = buffer.append_sequential(&ids, false, &self.state);
                let indent = buffer.space_width();
                buffer.append_boxed(
                    block,
                    Margin {
                        left: indent,
                        ..Default::default()
                    },
                    Rounding::same(1f32),
                    Color32::from_black_alpha(20),
                )
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let span = DefSpan {
                    from: *condition,
                    to: id,
                };
                let children = [
                    buffer.literal(TextLitKind::If),
                    self.append_def(buffer, *condition),
                ];
                let mut header = buffer.append_horizontal(&children, true);
                let then_body = self.append_def(buffer, *then_branch);
                let split = if let Some(else_branch) = else_branch {
                    // most of this is just needed for positioning the else-lit properly..
                    let else_lit = buffer.literal(TextLitKind::Else);
                    let header_size = buffer.size(header);
                    let mut then_body_size = buffer.size(then_body);
                    then_body_size.x = header_size.x.max(then_body_size.x);
                    buffer.set_size(then_body, then_body_size);
                    let offset = (then_body_size.x + DrawBuffer::INDENT * 2f32 - header_size.x)
                        .max(DrawBuffer::INDENT);
                    let branches = [then_body, self.append_def(buffer, *else_branch)];
                    let split = self.append_split(buffer, &branches, span, true);
                    let else_lit_size = buffer.size(else_lit);
                    header = buffer.append_inline(
                        [
                            RelativeDrawCallId::root(header),
                            RelativeDrawCallId::new(
                                else_lit,
                                Vec2::RIGHT * (header_size.x + offset),
                            ),
                        ]
                        .into(),
                        vec2(header_size.x + else_lit_size.x + offset, header_size.y),
                    );
                    split
                } else {
                    self.append_split(buffer, &[then_body], span, false)
                };
                buffer.append_sequential(&[header, split], false, &self.state)
            }
            Expr::Let { pat, expr } => self.append_let(buffer, *pat, None, Some(*expr), None),
            Expr::Match { expr, arms } => {
                let children = [
                    buffer.literal(TextLitKind::Match),
                    self.append_def(buffer, *expr),
                ];
                let header = buffer.append_horizontal(&children, true);
                let arms = Box::from_iter(arms.iter().map(|arm| {
                    let mut header = self.append_def(buffer, arm.pat);
                    if let Some(guard) = arm.guard {
                        let children = [
                            buffer.literal(TextLitKind::If),
                            self.append_def(buffer, guard),
                        ];
                        let guard = buffer.append_horizontal(&children, false);
                        header = buffer.append_sequential(&[header, guard], false, &self.state);
                    }
                    let children = [
                        buffer.append_boxed(
                            header,
                            Margin::same(2f32),
                            Rounding::same(1f32),
                            Color32::from_black_alpha(10),
                        ),
                        self.append_def(buffer, arm.expr),
                    ];
                    buffer.append_sequential(&children, false, &self.state)
                }));
                let span = DefSpan {
                    from: *expr,
                    to: id,
                };
                let branches = self.append_split(buffer, &arms, span, true);
                buffer.append_sequential(&[header, branches], false, &self.state)
            }
            Expr::Ref { expr, mutability } => self.append_ref(buffer, *expr, *mutability),
            Expr::UnaryOp { expr, op } => {
                let children = [
                    buffer.literal(TextLitKind::UnaryOp(*op)),
                    self.append_def(buffer, *expr),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::BinaryOp { lhs, rhs, op } => {
                let lhs_id = self.append_bracketed(buffer, *lhs, id);
                let rhs_id = self.append_bracketed(buffer, *rhs, id);
                let op_id = buffer.literal(TextLitKind::BinaryOp(*op));
                self.append_binary_op(
                    buffer,
                    lhs_id,
                    rhs_id,
                    op_id,
                    matches!(op, BinaryOp::Assignment { op: None }),
                )
            }
            Expr::Call { callee, args } => {
                let args = Box::from_iter(args.iter().map(|arg| self.append_def(buffer, *arg)));
                let args = self.append_args(buffer, &args);
                let children = [
                    self.append_def(buffer, *callee),
                    buffer.append_braced(args, BracketType::Round, Color32::BLACK),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::MethodCall {
                receiver,
                fn_name,
                args,
            } => {
                let receiver_call = self.append_bracketed(buffer, *receiver, id);
                let dot = buffer.literal(TextLitKind::Dot);
                let name = buffer.append_str(&fn_name);
                let args = Box::from_iter(args.iter().map(|arg| self.append_def(buffer, *arg)));
                let args = self.append_args(buffer, &args);
                let args = buffer.append_braced(args, BracketType::Round, Color32::BLACK);

                // FIXME: layouting should not be hard coded like this..
                let is_chained_call = matches!(
                    self.body.defs[*receiver],
                    Def::Expr(Expr::MethodCall { .. })
                );
                if buffer.is_complex(receiver_call) || is_chained_call {
                    let call = buffer.append_horizontal(&[dot, name, args], false);
                    let call = buffer.append_spaced(
                        call,
                        Margin {
                            left: 15f32,
                            ..Default::default()
                        },
                    );
                    buffer.append_sequential(&[receiver_call, call], false, &self.state)
                } else {
                    buffer.append_horizontal(&[receiver_call, dot, name, args], false)
                }
            }
            Expr::Field { expr, field } => {
                let children = [
                    self.append_def(buffer, *expr),
                    buffer.literal(TextLitKind::Dot),
                    buffer.append_str(&field),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::Loop { body, label } => {
                let children = [
                    self.append_labelled(buffer, TextLitKind::Loop, label.as_deref()),
                    self.append_def(buffer, *body),
                ];
                buffer.append_sequential(&children, false, &self.state)
            }
            Expr::Index { base, index_expr } => {
                let index = self.append_def(buffer, *index_expr);
                let children = [
                    self.append_def(buffer, *base),
                    buffer.append_braced(index, BracketType::Square, Color32::BLACK),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::Range {
                lhs,
                rhs,
                inclusive,
            } => {
                let range_lit = buffer.literal(TextLitKind::Range(*inclusive));
                match (self.append_opt(buffer, *lhs), self.append_opt(buffer, *rhs)) {
                    (Some(lhs), Some(rhs)) => {
                        if buffer.is_complex(lhs) || buffer.is_complex(rhs) {
                            let rhs = buffer.append_horizontal(&[range_lit, rhs], false);
                            buffer.append_sequential(&[lhs, rhs], false, &self.state)
                        } else {
                            buffer.append_horizontal(&[lhs, range_lit, rhs], false)
                        }
                    }
                    (None, Some(rhs)) => buffer.append_horizontal(&[range_lit, rhs], false),
                    (Some(lhs), None) => buffer.append_horizontal(&[lhs, range_lit], false),
                    (None, None) => range_lit,
                }
            }
            Expr::RecordLit {
                path,
                fields,
                spread,
                ellipsis,
            } => {
                let mut args = fields
                    .iter()
                    .map(|(name, expr)| {
                        let children = [
                            buffer.append_str(&name),
                            buffer.literal(TextLitKind::Colon),
                            buffer.space(),
                            self.append_def(buffer, *expr),
                        ];
                        buffer.append_horizontal(&children, false)
                    })
                    .collect_vec();
                if let Some(spread) = spread {
                    let children = [
                        buffer.literal(TextLitKind::Dots),
                        self.append_def(buffer, *spread),
                    ];
                    args.push(buffer.append_horizontal(&children, false));
                }
                if *ellipsis {
                    args.push(buffer.literal(TextLitKind::Dots));
                }
                let args = self.append_args(buffer, &args);
                let children = [
                    buffer.append_str(&path),
                    buffer.append_braced(args, BracketType::Round, Color32::BLACK),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::Return { expr } => {
                let id = buffer.literal(TextLitKind::Return);
                if let Some(expr) = expr {
                    let children = [id, buffer.space(), self.append_def(buffer, *expr)];
                    buffer.append_horizontal(&children, true)
                } else {
                    id
                }
            }
            Expr::Tuple { exprs } => self.append_tuple(buffer, &exprs, None),
            Expr::Closure {
                args,
                body_expr,
                capture_by,
                capture_dummy,
                return_dummy, // TODO?
                ..
            } => {
                let args = Box::from_iter(args.iter().map(|arg| self.append_def(buffer, *arg)));
                let args = self.append_args(buffer, &args);
                let args = buffer.append_braced(args, BracketType::Pipe, Color32::BLACK);
                let args = match capture_by {
                    CaptureBy::Value => {
                        let children = [buffer.literal(TextLitKind::Move), args];
                        buffer.append_horizontal(&children, false)
                    }
                    CaptureBy::Ref => args,
                };
                let body = self.append_def(buffer, *body_expr);
                let closure_call = if buffer.is_complex(args)
                    || buffer.is_complex(body)
                    || buffer.active_count(args, &self.state.liveliness) > 0
                    || buffer.active_count(body, &self.state.liveliness) > 0
                {
                    buffer.append_sequential(&[args, body], false, &self.state)
                } else {
                    let children = [args, buffer.space(), body];
                    buffer.append_horizontal(&children, false)
                };
                buffer.append_closure(closure_call, id, *capture_dummy, &self.state)
            }
            Expr::Array(arr) => {
                let id = match arr {
                    Array::ElementList { elements } => {
                        let elements = Box::from_iter(
                            elements.iter().map(|elem| self.append_def(buffer, *elem)),
                        );
                        self.append_args(buffer, &elements)
                    }
                    Array::Repeat {
                        initializer,
                        repeat,
                    } => {
                        let children = [
                            self.append_def(buffer, *initializer),
                            buffer.literal(TextLitKind::Semi),
                            self.append_def(buffer, *repeat),
                        ];
                        buffer.append_horizontal(&children, false)
                    }
                };
                buffer.append_braced(id, BracketType::Square, Color32::BLACK)
            }
            Expr::Box { expr } => {
                let children = [
                    buffer.literal(TextLitKind::Box),
                    self.append_def(buffer, *expr),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::Break { expr, label } => {
                let id = self.append_labelled(buffer, TextLitKind::Break, label.as_deref());
                if let Some(expr) = expr {
                    let children = [id, self.append_def(buffer, *expr)];
                    buffer.append_horizontal(&children, true)
                } else {
                    id
                }
            }
            Expr::Continue { label } => {
                self.append_labelled(buffer, TextLitKind::Continue, label.as_deref())
            }
            Expr::Missing | Expr::Unimplemented => buffer.append_str("<missing>"),
        }
    }

    fn append_pat(&self, buffer: &mut DrawBuffer, pat: &Pat, id: DefId) -> DrawCallId {
        match pat {
            Pat::Wild => buffer.literal(TextLitKind::Under),
            Pat::Path(path) => buffer.append_str(&path),
            Pat::Lit(def) => self.append_def(buffer, *def),
            Pat::Bind {
                annotation,
                binding_id,
                subpat,
            } => {
                let annotation = annotation
                    .map(|x| buffer.literal(TextLitKind::BindingAnnotation(x)))
                    .unwrap_or(buffer.noop());
                let binding = buffer.append_str(&self.body.bindings[*binding_id].name());
                if let Some(subpat) = self.append_opt(buffer, *subpat) {
                    let children = [annotation, binding, buffer.literal(TextLitKind::At), subpat];
                    buffer.append_horizontal(&children, false)
                } else {
                    buffer.append_horizontal(&[annotation, binding], false)
                }
            }
            Pat::Ref { pat, mutability } => self.append_ref(buffer, *pat, *mutability),
            Pat::Or { patterns } => {
                let pats = Box::from_iter(patterns.iter().enumerate().map(|(index, pat)| {
                    let id = self.append_def(buffer, *pat);
                    if index > 0 {
                        let or_drawer = buffer
                            .literal(TextLitKind::BinaryOp(BinaryOp::ArithOp(ArithOp::BitOr)));
                        buffer.append_horizontal(&[or_drawer, id], false)
                    } else {
                        id
                    }
                }));
                buffer.append_sequential(&pats, false, &self.state)
            }
            Pat::Tuple { pats, dots } => self.append_tuple(buffer, &pats, *dots),
            Pat::Record {
                path,
                args,
                ellipsis,
            } => {
                let mut args = args
                    .iter()
                    .map(|(name, id)| {
                        let children = [
                            buffer.append_str(&name),
                            buffer.literal(TextLitKind::Colon),
                            buffer.space(),
                            self.append_def(buffer, *id),
                        ];
                        buffer.append_horizontal(&children, false)
                    })
                    .collect_vec();
                if *ellipsis {
                    args.push(buffer.literal(TextLitKind::Dots));
                }
                let args = self.append_args(buffer, &args);
                let children = [
                    buffer.append_str(&path),
                    buffer.append_braced(args, BracketType::Square, Color32::BLACK),
                ];
                buffer.append_horizontal(&children, false)
            }
            Pat::TupleStruct {
                path,
                args,
                ellipsis,
            } => {
                let children = [
                    buffer.append_str(&path),
                    self.append_tuple(buffer, &args, *ellipsis),
                ];
                buffer.append_horizontal(&children, false)
            }
            Pat::Unimplemented => buffer.append_str("<missing>"),
        }
    }

    fn append_resugaring(
        &self,
        buffer: &mut DrawBuffer,
        resugaring: &Resugaring,
        id: DefId,
    ) -> DrawCallId {
        let selected = self
            .state
            .selected
            .map(|selected| selected == id)
            .unwrap_or(false);

        match resugaring {
            Resugaring::Macro(MacroResugaring { call, child_defs }) => {
                let child_active = child_defs
                    .iter()
                    .any(|child| self.state.liveliness.has_activity(*child));
                if selected || child_active {
                    return self.append_def_unsugared(buffer, id);
                }
                let call = buffer.append_str(&call);
                buffer.assoc_def_id(call, id); // here the association is actually real, compared to the other resugaring
                call
            }
            Resugaring::ForLoop(ForLoopResugaring {
                pat,
                iterable,
                body,
            }) => {
                if selected {
                    return self.append_def_unsugared(buffer, id);
                }
                let for_lit = buffer.literal(TextLitKind::For);
                buffer.fake_assoc_def_id(for_lit, id); // make the `for` literal selectable for expanding the resugaring
                let pat_id = self.append_def(buffer, *pat);
                let lhs = buffer.append_horizontal(&[for_lit, pat_id], false);
                let in_lit = buffer.literal(TextLitKind::In);
                let iterable_id = self.append_def(buffer, *iterable);
                let header = self.append_binary_op(buffer, lhs, iterable_id, in_lit, true);
                let body = self.append_def(buffer, *body);
                buffer.append_sequential(&[header, body], false, &self.state)
            }
            Resugaring::WhileLoop(WhileLoopResugaring { condition, body }) => {
                if selected {
                    return self.append_def_unsugared(buffer, id);
                }
                let while_lit = buffer.literal(TextLitKind::While);
                buffer.fake_assoc_def_id(while_lit, id); // make the `while` literal selectable for expanding the resugaring
                let children = [while_lit, self.append_def(buffer, *condition)];
                let header = buffer.append_horizontal(&children, true);
                let body = self.append_def_unsugared(buffer, *body);
                buffer.append_sequential(&[header, body], false, &self.state)
            }
            Resugaring::QuestionMark(QuestionMarkResugaring { expr }) => {
                if selected {
                    return self.append_def_unsugared(buffer, id);
                }
                let question_mark = buffer.literal(TextLitKind::QuestionMark);
                buffer.fake_assoc_def_id(question_mark, id); // make the `?` literal selectable for expanding the resugaring
                let children = [self.append_def(buffer, *expr), question_mark];
                buffer.append_horizontal(&children, true)
            }
        }
    }

    fn append_def_unsugared(&self, buffer: &mut DrawBuffer, id: DefId) -> DrawCallId {
        match &self.body.defs[id] {
            Def::Expr(expr) => self.append_expr(buffer, expr, id),
            Def::Pat(pat) => self.append_pat(buffer, pat, id),
            Def::Noop => buffer.noop(),
        }
    }

    fn append_def(&self, buffer: &mut DrawBuffer, id: DefId) -> DrawCallId {
        if let Some(resugaring) = self.body.expr_resugaring.get(id) {
            self.append_resugaring(buffer, resugaring, id)
        } else {
            let call = self.append_def_unsugared(buffer, id);
            buffer.assoc_def_id(call, id);
            call
        }
    }

    fn append_opt(&self, buffer: &mut DrawBuffer, id: Option<DefId>) -> Option<DrawCallId> {
        id.map(|id| self.append_def(buffer, id))
    }

    pub fn append_body(&self, buffer: &mut DrawBuffer) -> DrawCallId {
        let params = Box::from_iter(self.body.params.iter().map(|(pat, ty)| {
            let children = [
                self.append_def(buffer, *pat),
                buffer.literal(TextLitKind::Colon),
                buffer.space(),
                buffer.append_str(&ty),
            ];
            buffer.append_horizontal(&children, false)
        }));
        let params = self.append_args(buffer, &params);
        let params = buffer.append_braced(params, BracketType::Round, Color32::BLACK);

        let children = [
            buffer.literal(TextLitKind::Fn),
            buffer.append_str(&self.body.name),
            params,
        ];
        let header = buffer.append_horizontal(&children, false);
        let body = self.append_def(buffer, self.body.body_expr);

        // TODO: add an Expr::ReturnValue { binding, type_ref } ?
        let children = [
            buffer.literal(TextLitKind::Arrow),
            buffer.append_str(&self.body.return_type.1),
        ];
        let ret = buffer.append_horizontal(&children, false);
        buffer.assoc_def_id(ret, self.body.return_type.0);

        let id = buffer.append_sequential(&[header, body, ret], false, &self.state);
        let from_def = self
            .body
            .params
            .first()
            .map(|(id, _)| *id)
            .unwrap_or(self.body.body_expr);
        let id = buffer.append_linear_control_flow(id, from_def, &self.state);
        buffer.append_spaced(id, Margin::same(5f32))
    }
}

pub fn append_main_body<'a>(
    buffer: &mut DrawBuffer<'a>,
    body: &ThirBody,
    state: State,
) -> DrawCallId {
    let renderer = BodyRenderer { body, state };
    renderer.append_body(buffer)
}
