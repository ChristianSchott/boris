use std::iter;

use boris_shared::{
    ArithOp, Array, BinaryOp, BirBody, Block, CaptureBy, Def, DefId, DefSpan, Expr,
    ForLoopResugaring, MacroResugaring, Mutability, Pat, PathInfo, QuestionMarkResugaring,
    Resugaring, WhileLoopResugaring,
};
use eframe::{
    egui::Margin,
    epaint::{Color32, Rounding, Vec2},
};
use egui::vec2;
use itertools::Itertools;

use crate::drawer::{BracketType, DrawBuffer, DrawCallId, RelativeDrawCallId, State, TextLitKind};
struct BodyRenderer<'a> {
    body: &'a BirBody,
    state: State,
}

impl<'a> BodyRenderer<'a> {
    fn append_args(&self, buffer: &mut DrawBuffer, args: &[DrawCallId]) -> DrawCallId {
        if args.len() > 1 && args.iter().any(|arg| buffer.is_complex(*arg)) {
            buffer.append_sequential(args, false, &self.state)
        } else {
            let items = args
                .iter()
                .cloned()
                .interleave((1..args.len()).map(|_| buffer.cached_literal(TextLitKind::Comma)))
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
                let lhs_size = buffer.size(lhs_op_id);

                let size = buffer.size(rhs);
                let rect_id = buffer.append_rect(
                    Color32::from_black_alpha(10),
                    Rounding::ZERO,
                    size + Vec2::DOWN * lhs_size.y,
                );
                let rhs_id = buffer.append_inline(
                    [
                        RelativeDrawCallId::root(rect_id),
                        RelativeDrawCallId::root(rhs), // this is higher than the rect we allocate for this call, but thats intended in this case
                    ]
                    .into(),
                    size,
                );

                let left_rect = buffer.append_rect(
                    Color32::from_black_alpha(10),
                    Rounding::ZERO,
                    vec2(lhs_size.x, size.y),
                );
                let spaced_rhs = buffer.append_horizontal(&[left_rect, rhs_id], false);

                // let spaced_rhs = buffer.append_spaced(
                //     rhs_id,
                //     Margin {
                //         left: buffer.size(lhs_op_id).x,
                //         ..Default::default()
                //     },
                // );

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
    ) -> DrawCallId {
        let let_lit = buffer.cached_literal(TextLitKind::Let);
        let lhs = if let Some(type_ref) = type_ref {
            let children = [
                let_lit,
                self.append_def(buffer, pat),
                buffer.cached_literal(TextLitKind::Colon),
                buffer.space(),
                buffer.append_str(type_ref),
            ];
            buffer.append_horizontal(&children, true)
        } else {
            let children = [let_lit, self.append_def(buffer, pat)];
            buffer.append_horizontal(&children, true)
        };
        if let Some(init) = init {
            let rhs = self.append_def(buffer, init);
            let op =
                buffer.cached_literal(TextLitKind::BinaryOp(BinaryOp::Assignment { op: None }));
            self.append_binary_op(buffer, lhs, rhs, op, true)
        } else {
            lhs
        }
    }

    fn append_statement(&self, buffer: &mut DrawBuffer, statement: DrawCallId) -> DrawCallId {
        if buffer.is_complex(statement) {
            statement
        } else {
            let children = [statement, buffer.cached_literal(TextLitKind::Semi)];
            let id = buffer.append_horizontal(&children, false);
            const SPACE: f32 = 1f32;
            buffer.append_spaced(
                id,
                Margin {
                    top: SPACE,
                    bottom: SPACE,
                    ..Default::default()
                },
            )
        }
    }

    fn append_ref(&self, buffer: &mut DrawBuffer, id: DefId, mutability: Mutability) -> DrawCallId {
        let children = [
            buffer.cached_literal(TextLitKind::Ref(mutability)),
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
        let dots_id = buffer.cached_literal(TextLitKind::Dots);
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
        let lit = buffer.cached_literal(kind);
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

    fn append_if_arm(
        &self,
        buffer: &mut DrawBuffer,
        condition: DefId,
        then_branch: DefId,
        is_else_if: bool,
    ) -> DrawCallId {
        let if_lit = buffer.cached_literal(TextLitKind::If);
        let condition_id = self.append_def(buffer, condition);
        let header = if is_else_if {
            let else_lit = buffer.cached_literal(TextLitKind::Else);
            let space = buffer.space();
            buffer.append_horizontal(&[else_lit, space, if_lit, condition_id], true)
        } else {
            buffer.append_horizontal(&[if_lit, condition_id], true)
        };
        self.append_body(buffer, header, then_branch)
    }

    fn append_else_arm(
        &self,
        buffer: &mut DrawBuffer,
        else_branch: DefId,
        lit_dummy: DefId,
    ) -> DrawCallId {
        let else_lit = buffer.append_literal(TextLitKind::Else);
        buffer.assoc_def_id(else_lit, lit_dummy);
        self.append_body(buffer, else_lit, else_branch)
    }

    fn append_block(
        &self,
        buffer: &mut DrawBuffer,
        def_id: DefId,
        block: &Block,
        header: Option<DrawCallId>,
    ) -> DrawCallId {
        let mut ids = block
            .statements
            .iter()
            .map(|s| {
                let id = self.append_def(buffer, *s);
                self.append_statement(buffer, id)
            })
            .collect_vec();
        ids.extend(block.tail.iter().map(|id| self.append_def(buffer, *id)));
        let mut block_id = buffer.append_sequential(&ids, false, &self.state);
        block_id = buffer.indent(block_id);
        block_id = buffer.append_linear_control_flow(
            block_id,
            block.scope_start,
            Some(def_id),
            &self.state,
        );

        let open = header.unwrap_or_else(|| {
            buffer.id_literal(TextLitKind::CurlyBracket(true), block.scope_start)
        });
        let close = buffer.id_literal(TextLitKind::CurlyBracket(false), block.scope_end);
        buffer.append_sequential(&[open, block_id, close], false, &self.state)
    }

    fn append_body(&self, buffer: &mut DrawBuffer, header: DrawCallId, id: DefId) -> DrawCallId {
        if !self.body.expr_resugaring.contains_idx(id) {
            if let Def::Expr(Expr::Block(block)) = &self.body.defs[id] {
                let open_id = buffer.id_literal(TextLitKind::CurlyBracket(true), block.scope_start);
                let children = [header, buffer.space(), open_id];
                let header = buffer.append_horizontal(&children, true);
                return self.append_block(buffer, id, block, Some(header));
            }
        }
        let body_id = self.append_def(buffer, id);
        let children = [header, buffer.indent(body_id)];
        buffer.append_sequential(&children, false, &self.state)
    }

    fn append_expr(&self, buffer: &mut DrawBuffer, expr: &Expr, id: DefId) -> DrawCallId {
        match expr {
            Expr::Path(info) => match info {
                PathInfo::Binding(id) => buffer.append_str(&self.body.bindings[*id].name()),
                PathInfo::Path(path) => buffer.append_str(&path),
            },
            Expr::Literal(lit) => buffer.append_str(&lit),
            Expr::Block(block) => self.append_block(buffer, id, block, None),
            Expr::IfArm {
                condition,
                expr,
                else_if,
            } => self.append_if_arm(buffer, *condition, *expr, *else_if),
            Expr::ElseArm { expr, lit_dummy } => self.append_else_arm(buffer, *expr, *lit_dummy),
            Expr::Let { pat, expr } => self.append_let(buffer, *pat, None, Some(*expr)),
            Expr::LetStatement {
                pat,
                type_ref,
                initializer,
            } => self.append_let(buffer, *pat, type_ref.as_deref(), *initializer),
            Expr::Branch {
                entry_dummy,
                arms,
                full_defer,
            } => {
                let arms = Box::from_iter(arms.iter().map(|arm| {
                    let from = self.body.next_def_map[*arm]; // this may throw..
                    let arm_call = self.append_def_unsugared(buffer, *arm);
                    let arm_call =
                        buffer.append_linear_control_flow(arm_call, from, Some(*arm), &self.state);
                    (arm_call, from)
                }));
                let span = DefSpan {
                    from: *entry_dummy,
                    to: id,
                };
                buffer.append_branched(&arms, span, *full_defer, &self.state)
            }
            Expr::Match { expr, branch } => {
                let children = [
                    buffer.cached_literal(TextLitKind::Match),
                    self.append_def(buffer, *expr),
                    buffer.space(),
                    buffer.cached_literal(TextLitKind::CurlyBracket(true)),
                ];
                let body_id = self.append_def_unsugared(buffer, *branch);
                let close_id = buffer.id_literal(TextLitKind::CurlyBracket(false), id);
                let children = [
                    buffer.append_horizontal(&children, true),
                    buffer.append_spaced(
                        body_id,
                        Margin {
                            left: 5f32,
                            ..Default::default()
                        },
                    ),
                    close_id,
                ];
                buffer.append_sequential(&children, false, &self.state)
            }
            Expr::MatchArm {
                pat, guard, expr, ..
            } => {
                let mut header = self.append_def(buffer, *pat);
                if let Some(guard) = guard {
                    let children = [
                        buffer.cached_literal(TextLitKind::If),
                        self.append_def(buffer, *guard),
                    ];
                    let guard = buffer.append_horizontal(&children, false);
                    header = buffer.append_sequential(&[header, guard], false, &self.state);
                }
                let children = [header, buffer.cached_literal(TextLitKind::WideArrow)];
                header = buffer.append_horizontal(&children, true);
                header = buffer.append_boxed(
                    header,
                    Margin::same(2f32),
                    Rounding::same(1f32),
                    Color32::from_black_alpha(10),
                );
                self.append_body(buffer, header, *expr)
            }
            Expr::Ref { expr, mutability } => self.append_ref(buffer, *expr, *mutability),
            Expr::UnaryOp { expr, op } => {
                let children = [
                    buffer.cached_literal(TextLitKind::UnaryOp(*op)),
                    self.append_def(buffer, *expr),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::BinaryOp { lhs, rhs, op } => {
                let lhs_id = self.append_bracketed(buffer, *lhs, id);
                let rhs_id = self.append_bracketed(buffer, *rhs, id);
                let op_id = buffer.cached_literal(TextLitKind::BinaryOp(*op));
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
                let dot = buffer.cached_literal(TextLitKind::Dot);
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
                    buffer.cached_literal(TextLitKind::Dot),
                    buffer.append_str(&field),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::Loop { body, label } => {
                let header = self.append_labelled(buffer, TextLitKind::Loop, label.as_deref());
                let loop_id = self.append_body(buffer, header, *body);
                // TODO: add some looping cf here..
                buffer.append_boxed(
                    loop_id,
                    Margin::same(5f32),
                    Rounding::same(5f32),
                    Color32::from_black_alpha(10),
                )
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
                let range_lit = buffer.cached_literal(TextLitKind::Range(*inclusive));
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
                            buffer.cached_literal(TextLitKind::Colon),
                            buffer.space(),
                            self.append_def(buffer, *expr),
                        ];
                        buffer.append_horizontal(&children, false)
                    })
                    .collect_vec();
                if let Some(spread) = spread {
                    let children = [
                        buffer.cached_literal(TextLitKind::Dots),
                        self.append_def(buffer, *spread),
                    ];
                    args.push(buffer.append_horizontal(&children, false));
                }
                if *ellipsis {
                    args.push(buffer.cached_literal(TextLitKind::Dots));
                }
                let args = self.append_args(buffer, &args);
                let children = [
                    buffer.append_str(&path),
                    buffer.append_braced(args, BracketType::Curly, Color32::BLACK),
                ];
                buffer.append_horizontal(&children, false)
            }
            Expr::Return { expr } => {
                let id = buffer.cached_literal(TextLitKind::Return);
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
                return_dummy: _, // TODO?
                ..
            } => {
                let args = Box::from_iter(args.iter().map(|arg| self.append_def(buffer, *arg)));
                let mut args = self.append_args(buffer, &args);
                args = buffer.append_braced(args, BracketType::Pipe, Color32::BLACK);
                args = match capture_by {
                    CaptureBy::Value => {
                        let children = [buffer.cached_literal(TextLitKind::Move), args];
                        buffer.append_horizontal(&children, false)
                    }
                    CaptureBy::Ref => args,
                };

                let closure_call = if !buffer.is_complex(args)
                    && !(buffer.active_count(args, &self.state.liveliness) > 0)
                    && !matches!(self.body.defs[*body_expr], Def::Expr(Expr::Block(..)))
                {
                    let body = self.append_def(buffer, *body_expr);
                    if !buffer.is_complex(body)
                        && !(buffer.active_count(body, &self.state.liveliness) > 0)
                    {
                        let children = [args, buffer.space(), body];
                        buffer.append_horizontal(&children, false)
                    } else {
                        buffer.append_sequential(&[args, body], false, &self.state)
                    }
                } else {
                    self.append_body(buffer, args, *body_expr)
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
                            buffer.cached_literal(TextLitKind::Semi),
                            self.append_def(buffer, *repeat),
                        ];
                        buffer.append_horizontal(&children, false)
                    }
                };
                buffer.append_braced(id, BracketType::Square, Color32::BLACK)
            }
            Expr::Box { expr } => {
                let children = [
                    buffer.cached_literal(TextLitKind::Box),
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
            Pat::Wild => buffer.append_literal(TextLitKind::Under), // this can not be shared, as it is associated to a DefId
            Pat::Path(path) => buffer.append_str(&path),
            Pat::Lit(def) => self.append_def_unsugared(buffer, *def),
            Pat::Bind {
                annotation,
                binding_id,
                subpat,
            } => {
                let annotation = annotation
                    .map(|x| buffer.cached_literal(TextLitKind::BindingAnnotation(x)))
                    .unwrap_or(buffer.noop());
                let binding = buffer.append_str(&self.body.bindings[*binding_id].name());
                if let Some(subpat) = self.append_opt(buffer, *subpat) {
                    let children = [
                        annotation,
                        binding,
                        buffer.cached_literal(TextLitKind::At),
                        subpat,
                    ];
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
                        let or_drawer = buffer.cached_literal(TextLitKind::BinaryOp(
                            BinaryOp::ArithOp(ArithOp::BitOr),
                        ));
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
                            buffer.cached_literal(TextLitKind::Colon),
                            buffer.space(),
                            self.append_def(buffer, *id),
                        ];
                        buffer.append_horizontal(&children, false)
                    })
                    .collect_vec();
                if *ellipsis {
                    args.push(buffer.cached_literal(TextLitKind::Dots));
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
        let selected = self.state.selected.contains(&id);

        match resugaring {
            Resugaring::Macro(MacroResugaring { call, child_defs }) => {
                let active_children = child_defs
                    .iter()
                    .filter(|child| self.state.liveliness.has_activity(**child))
                    .count();
                if selected || active_children > 1 {
                    return self.append_def_unsugared(buffer, id);
                }
                let call = buffer.append_alias(&call, &child_defs);
                buffer.assoc_def_id(call, id); // here the association is actually real, compared to the other resugaring
                call
            }
            Resugaring::ForLoop(ForLoopResugaring {
                pat,
                iterable,
                body,
                scope,
            }) => {
                if selected {
                    return self.append_def_unsugared(buffer, id);
                }
                let for_lit = buffer.append_literal(TextLitKind::For);
                buffer.fake_assoc_def_id(for_lit, id); // make the `for` literal selectable for expanding the resugaring
                let pat_id = self.append_def(buffer, *pat);
                let lhs = buffer.append_horizontal(&[for_lit, pat_id], false);
                let in_lit = buffer.cached_literal(TextLitKind::In);
                let iterable_id = self.append_def(buffer, *iterable);
                let header = self.append_binary_op(buffer, lhs, iterable_id, in_lit, true);
                let body = self.append_body(buffer, header, *body);
                buffer.append_linear_control_flow(
                    body,
                    self.body.next_def_map[*iterable],
                    Some(*scope),
                    &self.state,
                )
            }
            Resugaring::WhileLoop(WhileLoopResugaring {
                condition,
                body,
                scope,
            }) => {
                if selected {
                    return self.append_def_unsugared(buffer, id);
                }
                let while_lit = buffer.append_literal(TextLitKind::While);
                buffer.fake_assoc_def_id(while_lit, id); // make the `while` literal selectable for expanding the resugaring
                let children = [while_lit, self.append_def(buffer, *condition)];
                let header = buffer.append_horizontal(&children, true);
                let body = self.append_body(buffer, header, *body);
                buffer.append_linear_control_flow(
                    body,
                    self.body.next_def_map[*condition],
                    Some(*scope),
                    &self.state,
                )
            }
            Resugaring::QuestionMark(QuestionMarkResugaring { expr }) => {
                if selected {
                    return self.append_def_unsugared(buffer, id);
                }
                let question_mark = buffer.append_literal(TextLitKind::QuestionMark);
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

    pub fn append_main_body(&self, buffer: &mut DrawBuffer) -> DrawCallId {
        let params = Box::from_iter(self.body.params.iter().map(|(pat, ty)| {
            let children = [
                self.append_def(buffer, *pat),
                buffer.cached_literal(TextLitKind::Colon),
                buffer.space(),
                buffer.append_str(&ty),
            ];
            buffer.append_horizontal(&children, false)
        }));
        let params = self.append_args(buffer, &params);
        let params = buffer.append_braced(params, BracketType::Round, Color32::BLACK);
        let fn_name_id = buffer.append_str(&self.body.name);
        buffer.assoc_def_id(fn_name_id, self.body.world_scope);
        let children = [buffer.cached_literal(TextLitKind::Fn), fn_name_id, params];
        let header = buffer.append_horizontal(&children, false);
        let body = self.append_body(buffer, header, self.body.body_expr);

        // TODO: add an Expr::ReturnValue { binding, type_ref } ?
        let children = [
            buffer.cached_literal(TextLitKind::Arrow),
            buffer.append_str(&self.body.return_type.1),
        ];
        let ret = buffer.append_horizontal(&children, false);
        buffer.assoc_def_id(ret, self.body.return_type.0);

        let id = buffer.append_sequential(&[body, ret], false, &self.state);
        let id = buffer.append_linear_control_flow(id, self.body.world_scope, None, &self.state);
        buffer.append_spaced(id, Margin::same(5f32))
    }
}

pub fn append_main_body<'a>(
    buffer: &mut DrawBuffer<'a>,
    body: &BirBody,
    state: State,
) -> DrawCallId {
    let renderer = BodyRenderer { body, state };
    renderer.append_main_body(buffer)
}
