use boris_shared::{
    ArithOp, Array, BinaryOp, Binding, BindingAnnotation, BindingId, BirBody, Block, CmpOp,
    Conflict, Def, DefEdgeKind, DefId, DefNode, DefSet, DefSpan, Expr, ForLoopResugaring, LogicOp,
    MacroResugaring, Mutability, Ordering, Pat, PathInfo, QuestionMarkResugaring, Resugaring,
    UnaryOp, WhileLoopResugaring,
};
use itertools::Itertools;
use la_arena::{Arena, ArenaMap};
use ra_ap_hir::{mir::MirLowerError, HasCrate, HirDisplay, InFile, TypeRef};
use ra_ap_hir_def::{
    body::{Body, BodySourceMap},
    hir::{self, ExprId, LabelId, PatId},
    lang_item::{self, LangItemTarget},
    path::Path,
    resolver::{resolver_for_expr, ValueNs},
    src::HasSource,
    DefWithBodyId, FunctionId,
};
use ra_ap_hir_ty::{db::HirDatabase, mir::MirSpan, InferenceResult, TyExt};
use ra_ap_syntax::{
    ast::{self, HasLoopBody, RangeOp},
    AstNode,
};
use smallvec::{smallvec, SmallVec};

use crate::body_walker::{walk_thir_body, EdgeKind, Node, NodeId, NodeKind};

pub fn create_thir_body<'a>(owner: FunctionId, db: &'a dyn HirDatabase) -> Result<BirBody, MirLowerError> {
    let (hir_body, hir_source_map) = db.body_with_source_map(owner.into());
    let infer = db.infer(owner.into());

    ThirBodyBuilder::new(owner, db, &hir_body, &hir_source_map, &infer).body()
}

pub(crate) struct ThirBodyBuilder<'a> {
    owner: FunctionId,
    db: &'a dyn HirDatabase,
    body: &'a Body,
    body_source_map: &'a BodySourceMap,
    infer: &'a InferenceResult,

    defs: Arena<Def>,
    expr_def_map: ArenaMap<ExprId, DefId>,
    pat_def_map: ArenaMap<PatId, DefId>,

    bindings: Arena<Binding>,
    binding_defs: ArenaMap<BindingId, SmallVec<[DefId; 1]>>,
    bindings_map: ArenaMap<hir::BindingId, BindingId>,
    binding_scopes: ArenaMap<BindingId, DefId>,

    body_def_id: DefId,
    param_def_ids: Vec<DefId>,
    world_scope_id: DefId,
    ret_def_id: DefId,
    ret_binding_id: BindingId,

    child_def_map: ArenaMap<DefId, SmallVec<[DefId; 1]>>,
    parent_def_map: ArenaMap<DefId, DefId>,

    next_def_map: ArenaMap<DefId, DefId>,
    def_sequence: ArenaMap<DefId, SmallVec<[DefId; 1]>>,
    def_sequence_inv: ArenaMap<DefId, SmallVec<[DefId; 1]>>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum BindingUsageHint {
    None,
    Arg(u32),
}

impl<'a> ThirBodyBuilder<'a> {
    pub fn map_expr(&self, hir_expr_id: hir::ExprId) -> DefId {
        self.expr_def_map.get(hir_expr_id).copied().unwrap()
    }

    pub fn map_pat(&self, hir_pat_id: hir::PatId) -> DefId {
        self.pat_def_map.get(hir_pat_id).copied().unwrap()
    }

    pub fn map_binding(&self, hir_binding_id: hir::BindingId) -> BindingId {
        self.bindings_map.get(hir_binding_id).copied().unwrap()
    }

    pub fn map_to_def(&self, span: MirSpan) -> Option<DefId> {
        Some(match span {
            MirSpan::ExprId(expr) => self.map_expr(expr),
            MirSpan::PatId(pat) => self.map_pat(pat),
            MirSpan::Unknown => return None,
        })
    }

    pub fn binding_def(&self, binding_id: BindingId) -> Option<DefId> {
        self.binding_defs
            .get(binding_id)
            .and_then(|defs| defs.first())
            .cloned()
    }

    pub fn marked_mut(&self, binding_id: BindingId) -> bool {
        match &self[binding_id] {
            Binding::Real { marked_mutable, .. } => *marked_mutable,
            Binding::Fake => false,
        }
    }

    pub fn binding_name(&self, binding_id: BindingId) -> &str {
        self[binding_id].name()
    }

    fn parent_def_map(defs: &Arena<Def>) -> ArenaMap<DefId, DefId> {
        let mut parent_map = ArenaMap::with_capacity(defs.len());

        for (def_id, def) in defs.iter() {
            let mut set_parent = |child_id: &DefId| {
                if let Some(old_parent) = parent_map.insert(*child_id, def_id) {
                    panic!(
                        "Expr {:?} has two parent exprs {:?} and {:?}.",
                        child_id, def_id, old_parent
                    );
                };
            };

            match def {
                Def::Expr(expr) => match expr {
                    Expr::Block(Block {
                        statements,
                        tail,
                        scope_start,
                        scope_end,
                    }) => {
                        set_parent(scope_start);
                        set_parent(scope_end);
                        for statement in statements.iter() {
                            set_parent(statement);
                        }
                        tail.iter().for_each(set_parent);
                    }
                    Expr::IfArm {
                        condition, expr, ..
                    } => {
                        set_parent(condition);
                        set_parent(expr);
                    }
                    Expr::Branch {
                        entry_dummy, arms, ..
                    } => {
                        set_parent(entry_dummy);
                        arms.iter().for_each(|arm| set_parent(arm));
                    }
                    Expr::Match { expr, branch } => {
                        set_parent(expr);
                        set_parent(branch);
                    }
                    Expr::MatchArm { pat, guard, expr, entry_dummy } => {
                        set_parent(entry_dummy);
                        set_parent(pat);
                        if let Some(guard) = guard {
                            set_parent(guard);
                        }
                        set_parent(expr);
                    }
                    Expr::BinaryOp { lhs, rhs, .. } => [lhs, rhs].into_iter().for_each(set_parent),
                    Expr::Call { callee, args } => {
                        [callee].into_iter().chain(args.iter()).for_each(set_parent);
                    }
                    Expr::MethodCall { receiver, args, .. } => {
                        [receiver]
                            .into_iter()
                            .chain(args.iter())
                            .for_each(set_parent);
                    }
                    Expr::Index { base, index_expr } => {
                        [base, index_expr].into_iter().for_each(set_parent);
                    }
                    Expr::Range { lhs, rhs, .. } => lhs.iter().chain(rhs).for_each(set_parent),
                    Expr::RecordLit { fields, spread, .. } => {
                        for (_, expr) in fields.iter() {
                            set_parent(expr);
                        }
                        spread.iter().for_each(set_parent);
                    }
                    Expr::Break { expr, .. } | Expr::Return { expr } => {
                        expr.iter().for_each(set_parent);
                    }
                    Expr::Tuple { exprs } => exprs.iter().for_each(set_parent),
                    Expr::Array(arr) => match arr {
                        Array::ElementList { elements } => {
                            elements.iter().for_each(set_parent);
                        }
                        Array::Repeat {
                            initializer,
                            repeat,
                        } => {
                            [initializer, repeat].into_iter().for_each(set_parent);
                        }
                    },
                    Expr::ElseArm { expr,lit_dummy }=>[expr, lit_dummy].into_iter().for_each(set_parent),
                    | Expr::Field { expr, .. }
                    | Expr::Loop { body: expr, .. }
                    | Expr::Ref { expr, .. }
                    | Expr::UnaryOp { expr, .. }
                    | Expr::Box { expr } => set_parent(expr),
                    Expr::Let { expr, pat, .. } => {
                        [expr, pat].into_iter().for_each(set_parent);
                    }
                    Expr::LetStatement {
                        pat, initializer, ..
                    } => {
                        set_parent(pat);
                        initializer.iter().for_each(set_parent);
                    }
                    Expr::Closure {
                        body_expr,
                        args,
                        capture_dummy,
                        capture_by: _,
                        return_dummy,
                        ..
                    } => {
                        set_parent(capture_dummy);
                        set_parent(body_expr);
                        set_parent(return_dummy);
                        args.iter().for_each(set_parent);
                    }
                    Expr::Missing
                    | Expr::Unimplemented
                    | Expr::Path(_)
                    | Expr::Literal(_)
                    | Expr::Continue { .. } => (),
                },
                Def::Pat(pat) => match pat {
                    Pat::Bind { subpat, .. } => subpat.iter().for_each(set_parent),
                    Pat::Ref { pat, .. } => set_parent(pat),
                    Pat::Record { args, .. } => {
                        for (_, pat) in args.iter() {
                            set_parent(pat);
                        }
                    }
                    Pat::Or { patterns: pats }
                    | Pat::Tuple { pats, .. }
                    | Pat::TupleStruct { args: pats, .. } => pats.iter().for_each(set_parent),
                    _ => (),
                },
                Def::Noop => (),
            }
        }
        parent_map
    }

    fn child_def_map(
        defs: &Arena<Def>,
        parent_map: &ArenaMap<DefId, DefId>,
    ) -> ArenaMap<DefId, SmallVec<[DefId; 1]>> {
        let mut child_pats: ArenaMap<DefId, SmallVec<[DefId; 1]>> = defs
            .iter()
            .map(|(id, _)| (id, smallvec::smallvec![]))
            .collect();
        for (def_id, _) in defs.iter() {
            if let Some(parent_id) = parent_map.get(def_id) {
                child_pats.entry(*parent_id).or_default().push(def_id);
            }
        }
        child_pats
    }

    pub fn parent_def(&self, def: DefId) -> Option<DefId> {
        self.parent_def_map.get(def).cloned()
    }

    pub fn child_defs(&self, def: DefId) -> Option<&'_ [DefId]> {
        self.child_def_map
            .get(def)
            .map(|children| children.as_slice())
    }

    pub fn return_binding(&self) -> BindingId {
        self.ret_binding_id
    }

    fn new(
        owner: FunctionId,
        db: &'a dyn HirDatabase,
        body: &'a Body,
        body_source_map: &'a BodySourceMap,
        infer: &'a InferenceResult,
    ) -> Self {
        let label_to_str =
            |label: LabelId| body.labels[label].name.display(db.upcast()).to_string();

        // 'flatten' exprs and pats arenas into a single defs arena
        let mut defs = Arena::with_capacity(body.exprs.len() + body.pats.len());
        let mut bindings = Arena::with_capacity(body.bindings.len());
        let expr_map: ArenaMap<_, _> = body
            .exprs
            .iter()
            .map(|(id, _)| (id, defs.alloc(Def::Expr(Expr::Unimplemented))))
            .collect();
        let pat_map: ArenaMap<_, _> = body
            .pats
            .iter()
            .map(|(id, _)| (id, defs.alloc(Def::Pat(Pat::Unimplemented))))
            .collect();
        let bindings_map: ArenaMap<_, _> = body
            .bindings
            .iter()
            .map(|(hir_id, binding)| {
                let id = bindings.alloc(Binding::Real {
                    name: binding.name.display(db.upcast()).to_string(),
                    marked_mutable: matches!(binding.mode, hir::BindingAnnotation::Mutable),
                });
                (hir_id, id)
            })
            .collect();
        let noop = |defs: &mut Arena<Def>| defs.alloc(Def::Noop);

        let map_expr = |hir_expr_id: hir::ExprId| expr_map.get(hir_expr_id).copied().unwrap();
        let map_pat = |hir_pat_id: hir::PatId| pat_map.get(hir_pat_id).copied().unwrap();
        let map_binding =
            |hir_binding_id: hir::BindingId| bindings_map.get(hir_binding_id).copied().unwrap();

        let mut binding_defs: ArenaMap<_, SmallVec<_>> = body
            .bindings
            .iter()
            .map(|(id, binding)| {
                let defs = binding
                    .definitions
                    .iter()
                    .map(|def| map_pat(*def))
                    .collect();
                (map_binding(id), defs)
            })
            .collect();

        let path_to_string = |path: &Path| -> String {
            match path {
                Path::LangItem(t, name) => {
                    let lang_item_name = match *t {
                        LangItemTarget::ImplDef(it) => format!("{:?}", it),
                        LangItemTarget::EnumId(it) => {
                            db.enum_data(it).name.display(db.upcast()).to_string()
                        }
                        LangItemTarget::Function(it) => {
                            db.function_data(it).name.display(db.upcast()).to_string()
                        }
                        LangItemTarget::Static(it) => {
                            db.static_data(it).name.display(db.upcast()).to_string()
                        }
                        LangItemTarget::Struct(it) => {
                            db.struct_data(it).name.display(db.upcast()).to_string()
                        }
                        LangItemTarget::Union(it) => {
                            db.union_data(it).name.display(db.upcast()).to_string()
                        }
                        LangItemTarget::TypeAlias(it) => {
                            db.type_alias_data(it).name.display(db.upcast()).to_string()
                        }
                        LangItemTarget::Trait(it) => {
                            db.trait_data(it).name.display(db.upcast()).to_string()
                        }
                        LangItemTarget::EnumVariant(it) => db
                            .enum_variant_data(it)
                            .name
                            .display(db.upcast())
                            .to_string(),
                    };
                    if let Some(name) = name {
                        format!("{}::{}", lang_item_name, name.display(db.upcast()))
                    } else {
                        format!("{}", lang_item_name)
                    }
                }
                Path::Normal { .. } => path.display(db).to_string(),
            }
        };

        let resolve_path = |id: hir::ExprId, path: &Path| -> PathInfo {
            let resolver = resolver_for_expr(db.upcast(), owner.into(), id);
            if let Some(ValueNs::LocalBinding(binding)) =
                resolver.resolve_path_in_value_ns_fully(db.upcast(), path)
            {
                PathInfo::Binding(map_binding(binding))
            } else {
                PathInfo::Path(path_to_string(path))
            }
        };

        let mut binding_scopes: ArenaMap<BindingId, DefId> = ArenaMap::default();
        let mut pat_scopes = vec![];
        for (hir_expr_id, expr) in body.exprs.iter() {
            let def_id = map_expr(hir_expr_id);

            defs[def_id] = Def::Expr(match expr {
                hir::Expr::Path(path) => Expr::Path(resolve_path(hir_expr_id, &path)),
                hir::Expr::Let { pat, expr } => Expr::Let {
                    pat: map_pat(*pat),
                    expr: map_expr(*expr),
                },
                hir::Expr::Block {
                    statements, tail, ..
                }
                | hir::Expr::Unsafe {
                    statements, tail, ..
                }
                | hir::Expr::Async {
                    statements, tail, ..
                } => {
                    let scope_start = noop(&mut defs);
                    let statements = statements
                        .iter()
                        .scan(scope_start, |last, stmnt| {
                            let id = match stmnt {
                                hir::Statement::Let {
                                    pat,
                                    initializer,
                                    type_ref,
                                    else_branch,
                                } => {
                                    let pat = map_pat(*pat);
                                    pat_scopes.push((pat, def_id));
                                    let let_expr = defs.alloc(Def::Expr(Expr::LetStatement {
                                        pat,
                                        type_ref: type_ref.as_ref().map(|ty_ref| {
                                            ty_ref.as_ref().display_truncated(db, None).to_string()
                                        }),
                                        initializer: initializer.map(map_expr),
                                    }));

                                    if let Some(else_branch) = else_branch {
                                        let lit_dummy = noop(&mut defs);
                                        let else_branch = defs.alloc(Def::Expr(Expr::ElseArm {
                                            expr: map_expr(*else_branch),lit_dummy,
                                        }));
                                        let entry_dummy = noop(&mut defs);
                                        defs.alloc(Def::Expr(Expr::Branch {
                                            entry_dummy,
                                            arms: [let_expr, else_branch].into(),
                                            full_defer: true,
                                        }))
                                    } else {
                                        let_expr
                                    }
                                }
                                hir::Statement::Expr { expr, .. } => map_expr(*expr),
                            };
                            *last = id;
                            Some(id)
                        })
                        .collect();
                    Expr::Block(Block {
                        scope_start,
                        scope_end: noop(&mut defs),
                        statements,
                        tail: tail.map(map_expr),
                    })
                }
                hir::Expr::Const(const_block_id) => {
                    let const_block = db.lookup_intern_anonymous_const(*const_block_id);
                    assert_eq!(const_block.parent, owner.into());
                    Expr::Block(Block {
                        scope_start: noop(&mut defs),
                        scope_end: noop(&mut defs),
                        statements: Default::default(),
                        tail: Some(map_expr(const_block.root)),
                    })
                }
                hir::Expr::Match { expr, arms } => {
                    let arms = Box::from_iter(arms.iter().map(|arm| {
                        let entry_dummy = noop(&mut defs); 
                        let pat = map_pat(arm.pat);
                        let arm = defs.alloc(Def::Expr(Expr::MatchArm {
                            entry_dummy,
                            pat,
                            guard: arm.guard.map(map_expr),
                            expr: map_expr(arm.expr),
                        }));
                        pat_scopes.push((pat, arm));
                        arm
                    }));
                    let expr = map_expr(*expr);
                    let entry_dummy = noop(&mut defs);
                    Expr::Match {
                        expr,
                        branch: defs.alloc(Def::Expr(Expr::Branch {
                            entry_dummy,
                            arms,
                            full_defer: true,
                        })),
                    }
                }
                hir::Expr::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    let cond_id = map_expr(*condition);
                    let if_arm = defs.alloc(Def::Expr(Expr::IfArm {
                        else_if: false,
                        condition: cond_id,
                        expr: map_expr(*then_branch),
                    }));
                    if let hir::Expr::Let { pat, .. } = &body.exprs[*condition] {
                        pat_scopes.push((map_pat(*pat), if_arm));
                    }
                    if let Some(else_branch) = else_branch {
                        let lit_dummy = noop(&mut defs);
                        let else_arm =defs.alloc(Def::Expr(Expr::ElseArm {
                            expr: map_expr(*else_branch),
                            lit_dummy,
                        }));
                        Expr::Branch {
                            entry_dummy: noop(&mut defs),
                            arms: [if_arm, else_arm].into(),
                            full_defer: true,
                        }
                    } else {
                        Expr::Branch {
                            entry_dummy: noop(&mut defs),
                            arms: [if_arm].into(),
                            full_defer: false,
                        }
                    }
                }
                hir::Expr::Ref {
                    expr, mutability, ..
                } => Expr::Ref {
                    expr: map_expr(*expr),
                    mutability: convert_mutability(mutability),
                },
                hir::Expr::UnaryOp { expr, op } => Expr::UnaryOp {
                    expr: map_expr(*expr),
                    op: convert_unary_op(*op),
                },
                hir::Expr::BinaryOp { lhs, rhs, op } => Expr::BinaryOp {
                    lhs: map_expr(*lhs),
                    rhs: map_expr(*rhs),
                    op: op
                        .map(convert_binary_op)
                        .unwrap_or(BinaryOp::ArithOp(ArithOp::Add)),
                },
                hir::Expr::Call { callee, args, .. } => Expr::Call {
                    callee: map_expr(*callee),
                    args: Box::from_iter(args.iter().map(|e| map_expr(*e))),
                },
                hir::Expr::MethodCall {
                    receiver,
                    args,
                    method_name,
                    ..
                } => Expr::MethodCall {
                    receiver: map_expr(*receiver),
                    fn_name: method_name.display(db.upcast()).to_string(),
                    args: Box::from_iter(args.iter().map(|e| map_expr(*e))),
                },
                hir::Expr::Literal(lt) => Expr::Literal(match lt {
                    hir::Literal::String(string) => {
                        format!("\"{}\"", string)
                    }
                    hir::Literal::CString(bytes) | hir::Literal::ByteString(bytes) => {
                        format!("\"[{}]\"", bytes.iter().map(|i| i.to_string()).join(","))
                    }
                    hir::Literal::Char(c) => format!("'{}'", c),
                    hir::Literal::Bool(b) => b.to_string(),
                    hir::Literal::Int(i, _) => i.to_string(),
                    hir::Literal::Uint(u, _) => u.to_string(),
                    hir::Literal::Float(f, _) => f.to_string(),
                }),
                hir::Expr::Field { expr, name } => Expr::Field {
                    expr: map_expr(*expr),
                    field: name.display(db.upcast()).to_string(),
                },
                hir::Expr::Loop { body, label } => Expr::Loop {
                    body: map_expr(*body),
                    label: label.map(label_to_str),
                },
                hir::Expr::Index { base, index, .. } => Expr::Index {
                    base: map_expr(*base),
                    index_expr: map_expr(*index),
                },
                hir::Expr::Range {
                    lhs,
                    rhs,
                    range_type,
                } => Expr::Range {
                    lhs: lhs.map(map_expr),
                    rhs: rhs.map(map_expr),
                    inclusive: matches!(range_type, RangeOp::Inclusive),
                },
                hir::Expr::RecordLit {
                    path,
                    fields,
                    ellipsis,
                    spread,
                    ..
                } => Expr::RecordLit {
                    path: path
                        .as_deref()
                        .map(|path| path_to_string(path))
                        .unwrap_or_default(),
                    fields: Box::from_iter(fields.iter().map(|field| {
                        (
                            field.name.display(db.upcast()).to_string(),
                            map_expr(field.expr),
                        )
                    })),
                    spread: spread.map(map_expr),
                    ellipsis: *ellipsis,
                },
                hir::Expr::Return { expr } => Expr::Return {
                    expr: expr.map(map_expr),
                },
                hir::Expr::Tuple { exprs, .. } => Expr::Tuple {
                    exprs: Box::from_iter(exprs.iter().map(|e| map_expr(*e))),
                },
                hir::Expr::Closure {
                    args,
                    body,
                    capture_by,
                    ..
                } => {
                    let ret_def_id = noop(&mut defs);
                    let ret_binding_id = bindings.alloc(Binding::Fake);
                    binding_defs.insert(ret_binding_id, smallvec![ret_def_id]);
                    binding_scopes.insert(ret_binding_id, ret_def_id);

                    let capture_def_id = noop(&mut defs);
                    let capture_binding_id = bindings.alloc(Binding::Fake);
                    binding_defs.insert(capture_binding_id, smallvec![capture_def_id]);
                    binding_scopes.insert(capture_binding_id, capture_def_id);

                    Expr::Closure {
                        capture_binding: capture_binding_id,
                        capture_dummy: capture_def_id,
                        args: if args.is_empty() {
                            // FIXME: with the new `capture_dummy` this is probably not needed anymore
                            // empty args cause problems during lt-span generation, so we insert a dummy def_id here..
                            Box::new([noop(&mut defs)])
                        } else {
                            Box::from_iter(args.iter().map(|arg| {
                                let pat = map_pat(*arg);
                                pat_scopes.push((pat, capture_def_id));
                                pat
                            }))
                        },
                        body_expr: map_expr(*body),
                        capture_by: match capture_by {
                            hir::CaptureBy::Value => boris_shared::CaptureBy::Value,
                            hir::CaptureBy::Ref => boris_shared::CaptureBy::Ref,
                        },
                        return_dummy: ret_def_id,
                        return_binding: ret_binding_id,
                    }
                }
                hir::Expr::Array(vals) => Expr::Array(match vals {
                    hir::Array::ElementList { elements, .. } => Array::ElementList {
                        elements: Box::from_iter(elements.iter().map(|e| map_expr(*e))),
                    },
                    hir::Array::Repeat {
                        initializer,
                        repeat,
                    } => Array::Repeat {
                        initializer: map_expr(*initializer),
                        repeat: map_expr(*repeat),
                    },
                }),
                hir::Expr::Box { expr } => Expr::Box {
                    expr: map_expr(*expr),
                },
                hir::Expr::Break { expr, label } => Expr::Break {
                    expr: expr.map(map_expr),
                    label: label.map(label_to_str),
                },
                hir::Expr::Continue { label } => Expr::Continue {
                    label: label.map(label_to_str),
                },
                hir::Expr::Missing => Expr::Missing,
                _ => {
                    println!("unimplemented {:?}", expr);
                    Expr::Unimplemented
                }
            });
        }

        for (hir_pat_id, pat) in body.pats.iter() {
            let def_id = map_pat(hir_pat_id);

            defs[def_id] = Def::Pat(match pat {
                hir::Pat::Wild => Pat::Wild,
                hir::Pat::Lit(expr) => Pat::Lit(map_expr(*expr)),
                hir::Pat::Bind { id, subpat } => Pat::Bind {
                    annotation: convert_binding_annotation(body.bindings[*id].mode),
                    binding_id: map_binding(*id),
                    subpat: subpat.map(map_pat),
                },
                hir::Pat::Ref { pat, mutability } => Pat::Ref {
                    pat: map_pat(*pat),
                    mutability: convert_mutability(mutability),
                },
                hir::Pat::Or(pats) => Pat::Or {
                    patterns: pats.iter().map(|pat| map_pat(*pat)).collect(),
                },
                hir::Pat::Path(path) => Pat::Path(path_to_string(&path)),
                hir::Pat::Tuple { args, ellipsis } => Pat::Tuple {
                    pats: args.iter().map(|p| map_pat(*p)).collect(),
                    dots: *ellipsis,
                },
                hir::Pat::Record {
                    path,
                    args,
                    ellipsis,
                } => Pat::Record {
                    path: path
                        .as_deref()
                        .map(|path| path_to_string(path))
                        .unwrap_or_default(),
                    args: args
                        .iter()
                        .map(|field| {
                            (
                                field.name.display(db.upcast()).to_string(),
                                map_pat(field.pat),
                            )
                        })
                        .collect(),
                    ellipsis: *ellipsis,
                },
                hir::Pat::TupleStruct {
                    path,
                    args,
                    ellipsis,
                } => Pat::TupleStruct {
                    path: path
                        .as_deref()
                        .map(|path| path_to_string(path))
                        .unwrap_or_default(),
                    args: args.iter().map(|field| map_pat(*field)).collect(),
                    ellipsis: *ellipsis,
                },
                hir::Pat::ConstBlock(block) => Pat::Lit(map_expr(*block)), // TODO: not quite correct
                // TODO: Range & Slice pats..
                _ => {
                    println!("Unhandled pattern {:?}", pat);
                    Pat::Unimplemented
                }
            });
        }

        let world_scope_id = noop(&mut defs);
        let ret_def_id = noop(&mut defs);
        let ret_binding_id = bindings.alloc(Binding::Fake);
        binding_defs.insert(ret_binding_id, smallvec![ret_def_id]);

        let body_def_id = map_expr(body.body_expr);
        let param_def_ids = body.params.iter().cloned().map(map_pat).collect_vec();
        let parent_def_map = Self::parent_def_map(&defs);
        let child_def_map = Self::child_def_map(&defs, &parent_def_map);

        // move this somewhere better..
        for (pat, owner) in pat_scopes {
            let mut stack = vec![pat];
            while let Some(top) = stack.pop() {
                if let Def::Pat(Pat::Bind { binding_id, .. }) = &defs[top] {
                    if let Some(scope) = binding_scopes.get(*binding_id) {
                        assert_eq!(*scope, owner, "Same binding owned by different scopes.");
                    } else {
                        binding_scopes.insert(*binding_id, owner);
                    }
                }
                if let Some(children) = child_def_map.get(top) {
                    stack.extend(children.iter());
                }
            }
        }

        let next_def_map = Self::next_control_flow_def_map(&defs);
        let def_sequence = Self::def_sequence(
            &defs,
            world_scope_id,
            &param_def_ids,
            body_def_id,
            ret_def_id,
        );
        let def_sequence_inv = Self::invert_sequence(&defs, &def_sequence);
        Self {
            owner,
            db,
            body,
            body_source_map,
            infer,
            defs,
            body_def_id,
            param_def_ids,
            world_scope_id,
            ret_def_id,
            ret_binding_id,
            parent_def_map,
            child_def_map,
            next_def_map,
            expr_def_map: expr_map,
            pat_def_map: pat_map,
            bindings,
            bindings_map,
            binding_defs,
            binding_scopes,
            def_sequence,
            def_sequence_inv,
        }
    }

    fn body(self) -> Result<BirBody, MirLowerError> {
        let data = self.db.function_data(self.owner);
        let name = data.name.display(self.db.upcast()).to_string();
        let ty_to_string = |type_ref: &TypeRef| -> String {
            type_ref.display_truncated(self.db, None).to_string()
        };
        let params = Box::from_iter(
            self.param_def_ids
                .iter()
                .zip(data.params.iter())
                .map(|(id, ty_ref)| (*id, ty_to_string(&ty_ref))),
        );
        let return_type = ty_to_string(&data.ret_type);
        let body_expr = self.map_expr(self.body.body_expr);
        let never_defs = self.never_defs();
        let def_order = self.def_ordering();

        let (def_graph, def_graph_inv, conflicts) = self.analyze_data_flow(&never_defs)?;

        let mut selectable_defs = DefSet::new(&self.defs);
        for (def, _) in def_graph.iter() {
            selectable_defs.set(def, true);
        }

        let expr_resugaring = self.expr_resugaring(&selectable_defs);
        // make resugar defs selectable, for showing the expansion..
        for (id, _) in expr_resugaring.iter() {
            selectable_defs.set(id, true);
        }

        Result::Ok(BirBody {
            name,
            params,
            world_scope: self.world_scope_id,
            return_type: (self.ret_def_id, return_type),
            body_expr,
            defs: self.defs,
            bindings: self.bindings,
            next_def_map: self.next_def_map,

            never_defs,
            selectable_defs,
            def_order,
            expr_resugaring,

            def_graph,
            def_graph_inv,
            conflicts,
        })
    }

    fn never_defs(&self) -> DefSet {
        let mut never_defs = DefSet::new(&self.defs);
        // init with all defs that have the never type
        let mut stack =
            self.body
                .exprs
                .iter()
                .filter_map(|(id, _)| self.infer[id].is_never().then_some(self.map_expr(id)))
                .chain(
                    self.body.pats.iter().filter_map(|(id, _)| {
                        self.infer[id].is_never().then_some(self.map_pat(id))
                    }),
                )
                .collect_vec();

        for top in stack {
            never_defs.set(top, true);
        }

        // extend until reaching some cf_branch..
        // while let Some(top) = stack.pop() {
        //     if never_defs[top] {
        //         continue;
        //     }
        //     never_defs.set(top, true);

        //     if let Some(next) = self.def_sequence.get(top) {
        //         stack.extend(
        //             next.iter()
        //                 .filter(|&id| {
        //                     match &self.defs[*id] {
        //                         Def::Expr(Expr::If {
        //                             then_branch,
        //                             else_branch,
        //                             ..
        //                         }) => {
        //                             // when if and else branch are never, then continue
        //                             never_defs[*then_branch]
        //                                 && else_branch.map(|id| never_defs[id]).unwrap_or(false)
        //                         }
        //                         Def::Expr(Expr::Match { arms, .. }) => {
        //                             // when all arms are never, then continue..
        //                             arms.iter().all(|arm| never_defs[*arm])
        //                         }
        //                         Def::Expr(Expr::Loop { .. }) => false, // FIXME: always stop at loop?
        //                         _ => true,
        //                     }
        //                 })
        //                 .copied(),
        //         );
        //     }
        // }
        never_defs
    }

    fn expr_resugaring(&self, selectable: &DefSet) -> ArenaMap<DefId, Resugaring> {
        let mut expr_resugar_map = ArenaMap::with_capacity(self.body.exprs.len());

        let expr_source = |id| {
            self.body_source_map.expr_syntax(id).map(|syntax| {
                let root = syntax.file_syntax(self.db.upcast());
                (syntax.file_id, syntax.value.to_node(&root))
            })
        };

        let crate_id = DefWithBodyId::from(self.owner).krate(self.db).into();
        let try_branch_item = self
            .db
            .lang_item(crate_id, lang_item::LangItem::TryTraitBranch);
        let into_iter_item = self
            .db
            .lang_item(crate_id, lang_item::LangItem::IntoIterIntoIter);

        for (id, expr) in self.body.exprs.iter() {
            match expr {
                hir::Expr::Match { expr, .. } => {
                    if let hir::Expr::Call { callee, args, .. } = &self.body.exprs[*expr] {
                        if let hir::Expr::Path(Path::LangItem(item, _)) = &self.body.exprs[*callee]
                        {
                            if Some(*item) == try_branch_item {
                                if let Some(expr) = args.first() {
                                    expr_resugar_map.insert(
                                        self.map_expr(id),
                                        Resugaring::QuestionMark(QuestionMarkResugaring {
                                            expr: self.map_expr(*expr),
                                        }),
                                    );
                                }
                            }

                            if Some(*item) == into_iter_item {
                                // TODO: do this without ast?
                                if let Ok((file_id, ast::Expr::ForExpr(for_expr))) = expr_source(id)
                                {
                                    if let (Some(pat), Some(it), Some(body)) = (
                                        for_expr.pat().and_then(|pat| {
                                            self.body_source_map
                                                .node_pat(InFile::new(file_id, &pat))
                                        }),
                                        for_expr.iterable().and_then(|it| {
                                            self.body_source_map
                                                .node_expr(InFile::new(file_id, &it))
                                        }),
                                        for_expr.loop_body().and_then(|body| {
                                            self.body_source_map.node_expr(InFile::new(
                                                file_id,
                                                &ast::Expr::BlockExpr(body),
                                            ))
                                        }),
                                    ) {
                                        let body = self.map_expr(body);
                                        expr_resugar_map.insert(
                                            self.map_expr(id),
                                            Resugaring::ForLoop(ForLoopResugaring {
                                                pat: self.map_pat(pat),
                                                iterable: self.map_expr(it),
                                                body,
                                                scope:self.parent_def_map[body],
                                            }),
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
                hir::Expr::Loop { body, .. }
                    if matches!(expr_source(id), Ok((_, ast::Expr::WhileExpr(_)))) =>
                {
                    if let hir::Expr::If {
                        condition,
                        then_branch,
                        ..
                    } = self.body.exprs[*body]
                    {
                        let body = self.map_expr(then_branch);
                        expr_resugar_map.insert(
                            self.map_expr(id),
                            Resugaring::WhileLoop(WhileLoopResugaring {
                                condition: self.map_expr(condition),
                                body,
                                scope:self.parent_def_map[body],
                            }),
                        );
                    }
                }
                _ => (),
            }
        }

        let fn_loc = self.db.lookup_intern_function(self.owner);
        let fn_src = fn_loc.source(self.db.upcast());
        for child in fn_src.syntax().value.descendants() {
            if let Some(macro_expr) = ast::MacroExpr::cast(child.clone()) {
                let in_file = InFile::new(fn_src.file_id, &macro_expr);
                if let Some(id) = self
                    .body_source_map
                    .macro_expansion_expr(in_file)
                    .map(|expr| self.map_expr(expr))
                {
                    let mut selectable_in_macro = vec![id];
                    let mut stack = vec![id];
                    while let Some(top) = stack.pop() {
                        if selectable[top] {
                            selectable_in_macro.push(top);
                        }
                        if let Some(child_defs) = self.child_defs(top) {
                            stack.extend_from_slice(child_defs);
                        }
                    }
                    expr_resugar_map.insert(
                        id,
                        Resugaring::Macro(MacroResugaring {
                            call: macro_expr.to_string(),
                            child_defs: selectable_in_macro,
                        }),
                    );
                }
            }
        }
        expr_resugar_map
    }

    pub fn next_control_flow_def_map(defs: &Arena<Def>) -> ArenaMap<DefId, DefId> {
        let first_child_def = |id: DefId| match &defs[id] {
            Def::Expr(expr) => match expr {
                Expr::Block(Block { scope_start,.. }) => Some(*scope_start),
                Expr::Range { lhs, rhs, .. } => lhs.or(*rhs),
                Expr::RecordLit { fields, spread, .. } => {
                    fields.first().map(|(_, def)| *def).or(*spread)
                }
                Expr::Break { expr, .. } | Expr::Return { expr } => expr.clone(),
                Expr::Tuple { exprs } => exprs.first().cloned(),
                Expr::Array(arr) => match arr {
                    Array::ElementList { elements } => elements.first().cloned(),
                    Array::Repeat { initializer, .. } => Some(*initializer),
                },
                Expr::BinaryOp { lhs, rhs, op } => {
                    Some(if matches!(op, boris_shared::BinaryOp::Assignment { .. }) {
                        *rhs
                    } else {
                        *lhs
                    })
                }
                Expr::Branch { entry_dummy, .. } => Some(*entry_dummy), 
                |Expr::LetStatement {  initializer, pat,.. }=>Some(initializer.unwrap_or(*pat)),
                Expr::Field { expr, .. }
                | Expr::Loop { body: expr, .. }
                | Expr::Ref { expr, .. }
                | Expr::UnaryOp { expr, .. }
                | Expr::Let { expr, .. }
                | Expr::Box { expr }
                | Expr::Match { expr, .. }
                | Expr::MatchArm { entry_dummy:expr, ..}
                | Expr::IfArm {
                    condition: expr, ..
                }| Expr::ElseArm { lit_dummy:expr,.. }
                | Expr::Call { callee: expr, .. }
                | Expr::MethodCall { receiver: expr, .. }
                | Expr::Index {
                    index_expr: expr, ..
                } => Some(*expr),
                Expr::Closure { .. } | //Some(args.first().copied().unwrap_or(*body_expr)),
                 Expr::Missing
                | Expr::Unimplemented
                | Expr::Path(_)
                | Expr::Literal(_)
                | Expr::Continue { .. } => None,
            },
            Def::Pat(pat) => match pat {
                Pat::Bind { subpat, .. } => *subpat,
                Pat::Ref { pat, .. } => Some(*pat),
                Pat::Record { args, .. } => args.first().map(|(_, def)| *def),
                Pat::Or { patterns: pats }
                | Pat::Tuple { pats, .. }
                | Pat::TupleStruct { args: pats, .. } => pats.first().cloned(),
                Pat::Wild | Pat::Path(_) | Pat::Lit(_) | Pat::Unimplemented => None,
            },
            Def::Noop => None,
        };
        let mut next_def_map = ArenaMap::with_capacity(defs.len());
        let mut stack = vec![];
        for (id, _) in defs.iter() {
            stack.clear();
            stack.push(id);
            // unwrap is safe here, as stack initially > 0, and no elements are removed
            while let Some(next) = first_child_def(*stack.last().unwrap()) {
                // abort early if `next` is already visited
                if let Some(first) = next_def_map.get(next) {
                    stack.push(*first);
                    break;
                }
                stack.push(next);
            }
            let first = *stack.last().unwrap();
            for def in stack.iter() {
                next_def_map.insert(*def, first);
            }
        }
        next_def_map
    }

    // map each def to an index, so the index of one def is smaller than another, if it lies before in the cfg.
    // If defs lie on different branches ordering is undefined.
    fn def_ordering(&self) -> ArenaMap<DefId, u32> {
        let mut order_map = ArenaMap::with_capacity(self.defs.len());

        // TODO: make this a non-recursive fn
        fn rec(
            map: &mut ArenaMap<DefId, u32>,
            defs: &Arena<Def>,
            def_id: DefId,
            mut counter: u32,
        ) -> u32 {
            let mut call = |child_id: DefId| {
                counter = rec(map, defs, child_id, counter);
            };

            match &defs[def_id] {
                Def::Expr(expr) => match expr {
                    Expr::Block(Block {
                        statements,
                        tail,
                        scope_start,
                        scope_end,
                    }) => {
                        call(*scope_start);
                        for statement in statements.iter() {
                            call(*statement);
                        }
                        if let Some(tail) = tail {
                            call(*tail);
                        }
                        call(*scope_end);
                    }
                    Expr::IfArm {
                        condition, expr, ..
                    } => {
                        call(*condition);
                        call(*expr);
                    }
                    Expr::ElseArm { expr,lit_dummy } => {
                        call(*lit_dummy);
                        call(*expr);
                    },
                    Expr::Let { pat, expr, .. } => {
                        call(*expr);
                        call(*pat);
                    }
                    Expr::LetStatement {
                        pat, initializer, ..
                    } => {
                        call(*pat);
                        if let Some(init) = initializer {
                            call(*init);
                        }
                    }
                    Expr::Match { expr, branch } => {
                        call(*expr);
                        call(*branch);
                    }
                    Expr::MatchArm { pat, guard, expr, entry_dummy } => {
                        call(*entry_dummy);
                        call(*pat);
                        if let Some(guard) = guard {
                            call(*guard);
                        }
                        call(*expr);
                    }
                    Expr::BinaryOp { lhs, rhs, op } => {
                        if matches!(op, BinaryOp::Assignment { .. }) {
                            call(*rhs);
                            call(*lhs);
                        } else {
                            call(*lhs);
                            call(*rhs);
                        }
                    }
                    Expr::MethodCall {
                        receiver: callee,
                        args,
                        ..
                    }
                    | Expr::Call { callee, args } => {
                        call(*callee);
                        for arg in args.iter() {
                            call(*arg);
                        }
                    }
                    Expr::Index { base, index_expr } => {
                        call(*base);
                        call(*index_expr);
                    }
                    Expr::Range { lhs, rhs, .. } => {
                        if let Some(lhs) = lhs {
                            call(*lhs);
                        }
                        if let Some(rhs) = rhs {
                            call(*rhs);
                        }
                    }
                    Expr::RecordLit { fields, spread, .. } => {
                        for (_, field) in fields.iter() {
                            call(*field);
                        }
                        if let Some(spread) = spread {
                            call(*spread);
                        }
                    }
                    Expr::Tuple { exprs } => {
                        for expr in exprs.iter() {
                            call(*expr);
                        }
                    }
                    Expr::Closure {
                        capture_dummy,
                        args,
                        body_expr,
                        return_dummy,
                        ..
                    } => {
                        call(*capture_dummy);
                        for arg in args.iter() {
                            call(*arg);
                        }
                        call(*body_expr);
                        call(*return_dummy);
                    }
                    Expr::Array(arr) => match arr {
                        Array::ElementList { elements } => {
                            for elem in elements.iter() {
                                call(*elem);
                            }
                        }
                        Array::Repeat {
                            initializer,
                            repeat,
                        } => {
                            call(*initializer);
                            call(*repeat);
                        }
                    },
                    Expr::UnaryOp { expr, .. }
                    | Expr::Ref { expr, .. }
                    | Expr::Field { expr, .. }
                    | Expr::Loop { body: expr, .. }
                    | Expr::Box { expr } => call(*expr),
                    Expr::Return { expr } | Expr::Break { expr, .. } => {
                        if let Some(expr) = expr {
                            call(*expr);
                        }
                    }
                    Expr::Branch { entry_dummy, arms, .. } => { 
                        call(*entry_dummy);
                        arms.iter().cloned().for_each(call);
                    },
                    Expr::Path(_)
                    | Expr::Literal(_)
                    | Expr::Continue { .. }
                    | Expr::Missing
                    | Expr::Unimplemented => (),
                },
                Def::Pat(pat) => match pat {
                    Pat::Lit(lit) => call(*lit),
                    Pat::Bind { subpat, .. } => {
                        if let Some(subpat) = subpat {
                            call(*subpat);
                        }
                    }
                    Pat::Ref { pat, .. } => call(*pat),
                    Pat::Record { args, .. } => {
                        for (_, arg) in args.iter() {
                            call(*arg);
                        }
                    }
                    Pat::Or { patterns: args }
                    | Pat::Tuple { pats: args, .. }
                    | Pat::TupleStruct { args, .. } => {
                        for arg in args.iter() {
                            call(*arg);
                        }
                    }
                    _ => (),
                },
                Def::Noop => (),
            }
            map.insert(def_id, counter);
            counter + 1
        }

        std::iter::once(self.world_scope_id)
            .chain(self.param_def_ids.iter().cloned())
            .chain(std::iter::once(self.body_def_id))
            .chain(std::iter::once(self.ret_def_id))
            .fold(0, |counter, def_id| {
                rec(&mut order_map, &self.defs, def_id, counter)
            });

        // for (def, index) in order_map.iter() {
        //     println!("{:?}:\t  {index}", self.defs[def]);
        // }

        order_map
    }

    fn def_sequence(
        defs: &Arena<Def>,
        world_scope: DefId,
        params: &[DefId],
        body: DefId,
        ret: DefId,
    ) -> ArenaMap<DefId, SmallVec<[DefId; 1]>> {
        fn push_params_and_body(
            stack: &mut Vec<(Option<DefId>, DefId)>,
            params: &[DefId],
            body: DefId,
            last_def: Option<DefId>,
        ) {
            if params.is_empty() {
                stack.push((last_def, body));
                return;
            }
            stack.push((last_def, *params.first().unwrap()));
            for pairs in params.windows(2) {
                stack.push((Some(pairs[0]), pairs[1]));
            }
            if let Some(last_param) = params.last().cloned() {
                stack.push((Some(last_param), body));
            }
        }

        let mut sequence_map: ArenaMap<DefId, SmallVec<[DefId; 1]>> =
            ArenaMap::with_capacity(defs.len());
        let mut connect = |from: DefId, to: DefId| {
            sequence_map.entry(from).or_default().push(to);
        };

        let mut stack: Vec<(Option<DefId>, DefId)> = vec![];

        connect(body, ret);
        push_params_and_body(&mut stack, params, body, Some(world_scope));

        while let Some((last_expr, next_child)) = stack.pop() {
            let mut set_sequence = |children: &[DefId]| {
                if children.is_empty() {
                    if let Some(last_expr) = last_expr {
                        connect(last_expr, next_child);
                    }
                } else {
                    stack.push((last_expr, *children.first().unwrap()));
                    for pairs in children.windows(2) {
                        stack.push((Some(pairs[0]), pairs[1]));
                    }
                    if let Some(last_child) = children.last() {
                        connect(*last_child, next_child);
                    }
                }
            };
            match &defs[next_child] {
                Def::Expr(expr) => match expr {
                    Expr::Block(Block {
                        statements,
                        tail,
                        scope_start,
                        scope_end,
                    }) => {
                        let mut defs = vec![*scope_start];
                        defs.extend(statements.iter());
                        defs.extend(tail.iter().cloned());
                        defs.push(*scope_end);
                        set_sequence(&defs);
                    }
                    Expr::Branch {
                        entry_dummy,
                        arms, full_defer, ..
                    } => {
                        stack.push((last_expr, *entry_dummy));
                        for arm in arms.iter() {
                            stack.push((Some(*entry_dummy), *arm));
                            connect(*arm, next_child);
                        }
                        if !*full_defer {
                            // add a skip connection
                            if let Some(last_expr) = last_expr {
                                connect(last_expr, next_child);
                            }
                        }
                    }
                    Expr::IfArm {
                        condition, expr, ..
                    } => {
                        set_sequence(&[*condition, *expr]);
                    }
                    Expr::Match { expr, branch } => {
                        set_sequence(&[*expr, *branch]);
                    }
                    Expr::MatchArm { entry_dummy, pat, guard, expr } => {
                        if let Some(guard_expr) = guard {
                            set_sequence(&[*entry_dummy, *pat, *guard_expr, *expr]);
                        } else {
                            set_sequence(&[*entry_dummy, *pat, *expr]);
                        }
                    }
                    Expr::BinaryOp { lhs, rhs, op } => {
                        if matches!(op, boris_shared::BinaryOp::Assignment { .. }) {
                            set_sequence(&[*rhs, *lhs]);
                        } else {
                            set_sequence(&[*lhs, *rhs]);
                        }
                    }
                    Expr::Call {
                        callee: receiver,
                        args,
                    }
                    | Expr::MethodCall { receiver, args, .. } => set_sequence(
                        &[*receiver]
                            .into_iter()
                            .chain(args.iter().cloned())
                            .collect_vec(),
                    ),
                    Expr::Index { base, index_expr } => set_sequence(&[*base, *index_expr]),
                    Expr::Range { lhs, rhs, .. } => {
                        set_sequence(&lhs.clone().into_iter().chain(rhs.clone()).collect_vec());
                    }
                    Expr::RecordLit { fields, spread, .. } => set_sequence(
                        &fields
                            .iter()
                            .map(|(_, val_expr)| *val_expr)
                            .chain(spread.clone().into_iter())
                            .collect_vec(),
                    ),
                   
                    Expr::Tuple { exprs } => set_sequence(&exprs),
                    Expr::Array(arr) => match arr {
                        Array::ElementList { elements } => set_sequence(&elements),
                        Array::Repeat {
                            initializer,
                            repeat,
                        } => set_sequence(&[*initializer, *repeat]),
                    },
                    Expr::Let { pat, expr } => set_sequence(&[*expr, *pat]),
                    Expr::LetStatement {
                        pat, initializer, ..
                    } => {
                        if let Some(init) = initializer {
                            set_sequence(&[*init, *pat]);
                        } else {
                            set_sequence(&[*pat]);
                        }
                    }
                    Expr::Loop { body, .. }=>{
                        // TODO: create a looping connection to the beginning?
                        set_sequence(&[*body]);
                    }
                    Expr::Break { expr, .. } | Expr::Return { expr } => {
                        // TODO: connect to wherever the break points to?
                        set_sequence(&expr.clone().into_iter().collect_vec());
                    }
                    Expr::ElseArm { expr ,lit_dummy}=>{
                        set_sequence(&[*lit_dummy,*expr]);
                    },
                    | Expr::Field { expr, .. }
                    | Expr::Ref { expr, .. }
                    | Expr::UnaryOp { expr, .. }
                    | Expr::Box { expr } => set_sequence(&[*expr]),
                    Expr::Closure {
                        capture_dummy,
                        args,
                        body_expr,
                        return_dummy,
                        ..
                    } => {
                        set_sequence(&[]);
                        push_params_and_body(&mut stack, &args, *body_expr, Some(*capture_dummy));
                        connect(*body_expr, *return_dummy);
                        // connect(*body_expr, next_child);
                    }
                    Expr::Missing
                    | Expr::Unimplemented
                    | Expr::Path(_)
                    | Expr::Literal(_)
                    | Expr::Continue { .. } => set_sequence(&[]),
                },
                Def::Pat(pat) => match pat {
                    Pat::Lit(expr_id) => set_sequence(&[*expr_id]),
                    Pat::Bind { subpat, .. } => {
                        set_sequence(&subpat.clone().into_iter().collect_vec());
                    }
                    Pat::Ref { pat, .. } => set_sequence(&[*pat]),
                    Pat::Or { patterns } => set_sequence(&patterns),
                    Pat::Tuple { pats, .. } => set_sequence(&pats),
                    Pat::Record { args, .. } => {
                        set_sequence(&args.iter().map(|(_, pat)| *pat).collect_vec());
                    }
                    Pat::TupleStruct { args, .. } => set_sequence(&args),
                    Pat::Path(_) | Pat::Wild | Pat::Unimplemented => set_sequence(&[]),
                },
                Def::Noop => set_sequence(&[]),
            }
        }
        sequence_map
    }

    fn invert_sequence(
        defs: &Arena<Def>,
        map: &ArenaMap<DefId, SmallVec<[DefId; 1]>>,
    ) -> ArenaMap<DefId, SmallVec<[DefId; 1]>> {
        let mut inverted_map: ArenaMap<DefId, SmallVec<[DefId; 1]>> =
            ArenaMap::with_capacity(defs.len());
        for (from_id, to_ids) in map.iter() {
            for to_id in to_ids.iter() {
                inverted_map.entry(*to_id).or_default().push(from_id);
            }
        }
        inverted_map
    }

    pub fn find_binding_usage(
        &self,
        def_id: DefId,
        binding_id: BindingId,
        hint: BindingUsageHint,
    ) -> Option<DefId> {
        let mut stack = vec![def_id];
        while let Some(top) = stack.pop() {
            match &self.defs[top] {
                Def::Expr(expr) => match expr {
                    Expr::Path(info) => match info {
                        PathInfo::Binding(id) if binding_id == *id => {
                            return Some(top);
                        }
                        _ => (),
                    },
                    _ => {
                        if let BindingUsageHint::Arg(index) = hint {
                            let mut args = match expr {
                                Expr::BinaryOp { lhs, rhs, .. } => {
                                    vec![*lhs, *rhs]
                                }
                                Expr::Call { args, .. } => args.iter().cloned().collect(),
                                Expr::MethodCall { receiver, args, .. } => {
                                    let mut args: Vec<_> = args.iter().cloned().collect();
                                    args.insert(0, *receiver);
                                    args
                                }
                                Expr::Range { lhs, rhs, .. } => {
                                    lhs.iter().chain(rhs.iter()).cloned().collect()
                                }
                                Expr::RecordLit { fields, spread, .. } => fields
                                    .iter()
                                    .map(|(_, id)| *id)
                                    .chain(spread.iter().cloned())
                                    .collect(),
                                Expr::Tuple { exprs } => exprs.iter().cloned().collect(),
                                Expr::Array(arr) => match arr {
                                    Array::ElementList { elements } => {
                                        elements.iter().cloned().collect()
                                    }
                                    Array::Repeat {
                                        initializer,
                                        repeat,
                                    } => vec![*initializer, *repeat],
                                },
                                _ => vec![],
                            };
                            if index < args.len() as u32 {
                                let preferred = args[index as usize];
                                args.remove(index as usize);
                                stack.extend_from_slice(&args);
                                stack.push(preferred); // visit the hinted child first
                                continue;
                            }
                        }
                        if let Some(children) = self.child_def_map.get(top) {
                            stack.extend(
                                children
                                    .iter()
                                    .filter(|&id| matches!(self.defs[*id], Def::Expr(_))),
                            );
                        }
                    }
                },
                Def::Pat(_) => {
                    // usage must originate from right side of a let expression/ statement
                    // -> move up to next expr
                    let mut id = Some(top);
                    while let Some(Def::Pat(_)) = id.map(|id| &self.defs[id]) {
                        id = id.and_then(|id| self.parent_def_map.get(id).copied());
                    }
                    if let Some(id) = id {
                        match &self.defs[id] {
                            Def::Expr(Expr::Let { expr, .. })
                            | Def::Expr(Expr::Match { expr, .. }) => stack.push(*expr),
                            Def::Expr(Expr::MatchArm { .. }) => {
                                // go up two levels: MatchArm -> Branch -> Match
                                if let Some(Def::Expr(Expr::Match { expr, .. })) = self
                                    .parent_def(id)
                                    .and_then(|id| self.parent_def(id))
                                    .map(|parent| &self.defs[parent])
                                {
                                    stack.push(*expr);
                                }
                            }
                            Def::Expr(Expr::LetStatement {
                                initializer: Some(init),
                                ..
                            }) => {
                                stack.push(*init);
                            }
                            _ => (),
                        }
                    }
                }
                Def::Noop => (),
            }
        }
        println!("failed finding binding usage");
        None
    }

    pub fn find_binding_assignment(&self, def_id: DefId, binding_id: BindingId) -> Option<DefId> {
        if matches!(self.bindings[binding_id], Binding::Fake) {
            // this is a dummy binding, thus is can't be found (this is currently only used for return values)
            return self.binding_def(binding_id);
        }

        let mut stack = vec![def_id];
        while let Some(top) = stack.pop() {
            match &self.defs[top] {
                Def::Expr(Expr::Path(PathInfo::Binding(id)))
                | Def::Pat(Pat::Bind { binding_id: id, .. })
                    if *id == binding_id =>
                {
                    return Some(top);
                }
                Def::Expr(Expr::BinaryOp {
                    lhs,
                    op: boris_shared::BinaryOp::Assignment { op: None },
                    ..
                }) => {
                    stack.push(*lhs); // only search in lhs. rhs can not be the assignment
                }
                _ => {
                    if let Some(children) = self.child_def_map.get(top) {
                        stack.extend(children.iter());
                    }
                }
            }
        }

        println!(
            "failed finding assignment to binding '{}' ({}) in '{:?}'",
            self.binding_name(binding_id),
            binding_id.into_raw().into_u32(),
            self.defs[def_id]
        );
        None
    }

    pub fn find_drop_def(&self, def_id: DefId) -> DefId {
        // println!("drop def {:?}", self.defs[def_id]);
        match &self[def_id] {
            Def::Expr(Expr::Block(Block { scope_end, .. })) => *scope_end,
            Def::Expr(Expr::Closure { return_dummy, .. }) => *return_dummy, // not sure if this is needed..
            _ => def_id,
        }
    }

    fn analyze_data_flow(
        &self,
        never_def_set: &DefSet,
    ) -> Result<(
        ArenaMap<DefId, DefNode>,
        ArenaMap<DefId, SmallVec<[DefId; 1]>>,
        ArenaMap<DefId, Vec<Conflict>>,
    ), MirLowerError> {
        let following_defs =
            |def_id: DefId, sequence: &ArenaMap<DefId, SmallVec<[DefId; 1]>>| -> DefSet {
                let mut following = DefSet::new(&self.defs);
                let mut stack = vec![def_id];
                while let Some(top) = stack.pop() {
                    if never_def_set[top] || following[top] {
                        continue;
                    }
                    following.set(top, true);
                    if let Some(next) = sequence.get(top) {
                        stack.extend(next.iter());
                    }
                }
                following
            };

        let graph = walk_thir_body(self, self.db, self.owner)?;

        let track_ref = |node: NodeId| {
            let mut defs = vec![];
            let mut target_defs = DefSet::new(&self.defs); // just track which defs have been added already

            let mut stack = vec![node];
            while let Some(top) = stack.pop() {
                for lt in graph[top]
                    .lifetimes
                    .iter()
                    .filter_map(|lt| graph.constraints.get(*lt))
                    .flatten()
                {
                    if let Some(nodes) = graph.lifetime_nodes.get(*lt) {
                        for node in nodes {
                            if let Node {
                                kind: NodeKind::Place { .. } | NodeKind::Deref { .. },
                                span: Some(def),
                                ..
                            } = &graph[*node]
                            {
                                if !target_defs.contains(*def) {
                                    target_defs.set(*def, true);
                                    defs.push((DefEdgeKind::Lifetime, *def));
                                }
                            } else {
                                stack.push(*node);
                            }
                        }
                    }
                }
            }
            defs
        };

        let mut def_graph: ArenaMap<DefId, DefNode> = ArenaMap::with_capacity(self.defs.len());
        for (node_id, node) in graph.nodes.iter() {
            if let Some(def) = node.span {
                match &node.kind {
                    NodeKind::Place(Some(binding), is_root) => {
                        let mut def_scope = DefSet::new(&self.defs);

                        let edges = graph
                            .edges
                            .get(node_id)
                            .map(|edges| {
                                edges
                                    .iter()
                                    .filter_map(|edge| {
                                        if let Some(span) = graph[edge.to].span {
                                            // limit scope
                                            if match &edge.kind {
                                                EdgeKind::Move => *is_root,
                                                EdgeKind::EndScope => true,
                                                EdgeKind::Reassign => true,
                                                _ => false,
                                            } {
                                                def_scope
                                                    .or(&following_defs(span, &self.def_sequence));
                                            }

                                            match &edge.kind {
                                                EdgeKind::Ref(mutable) => {
                                                    Some((DefEdgeKind::Ref(*mutable), span))
                                                }
                                                EdgeKind::Move => {
                                                    Some((DefEdgeKind::Move(!*is_root), span))
                                                }
                                                EdgeKind::Copy => Some((DefEdgeKind::Copy, span)),
                                                EdgeKind::Deref => Some((DefEdgeKind::Deref, span)),
                                                EdgeKind::Reassign => {
                                                    Some((DefEdgeKind::Reassign, span))
                                                }
                                                EdgeKind::EndScope => None,
                                                _ => None,
                                            }
                                        } else {
                                            None
                                        }
                                    })
                                    .collect_vec()
                            })
                            .unwrap_or_default();

                        let mut defs_after_init = following_defs(def, &self.def_sequence);
                        defs_after_init.and(&def_scope.inverted());

                        def_graph
                            .entry(def)
                            .and_modify(|node| {
                                node.active.or(&defs_after_init);

                                for (kind, to) in edges.iter() {
                                    if !node.edges.iter().any(|(_, edge_to)| edge_to == to) {
                                        node.edges.push((kind.clone(), *to));
                                    }
                                }
                            })
                            .or_insert_with(|| DefNode {
                                kind: boris_shared::NodeKind::Source {
                                    mutable: self.marked_mut(*binding),
                                    binding: *binding,
                                    contains_lt: !node.lifetimes.is_empty(),
                                    scope: self.binding_scopes.get(*binding).copied(),
                                },
                                edges,
                                active: defs_after_init,
                            });
                    }
                    NodeKind::Deref { .. } | NodeKind::Value => {
                        def_graph.entry(def).or_insert_with(|| DefNode {
                            kind: boris_shared::NodeKind::Usage,
                            edges: track_ref(node_id),
                            active: following_defs(def, &self.def_sequence_inv),
                        });
                    }
                    _ => (),
                }
            }
        }

        // inverted def graph
        let mut def_graph_inv: ArenaMap<_, SmallVec<[DefId; 1]>> =
            ArenaMap::with_capacity(self.defs.len());
        for (id, node) in def_graph.iter() {
            for (_, to) in node.edges.iter() {
                def_graph_inv.entry(*to).or_default().push(id);
            }
        }

        // gather conflicts and resolve from node_ids to def_ids
        let mut conflicts: ArenaMap<DefId, Vec<_>> = ArenaMap::new();
        for conflict in graph.conflicts.iter() {
            if let Some(from) = graph.span(conflict.from) {
                conflicts.entry(from).or_default().push(Conflict {
                    kind: conflict.kind,
                    targets: conflict
                        .targets
                        .iter()
                        .filter_map(|id| graph.span(*id))
                        .collect(),
                });
            }
        }

        Result::Ok((def_graph, def_graph_inv, conflicts))
    }
}

impl<'a> std::ops::Index<BindingId> for ThirBodyBuilder<'a> {
    type Output = Binding;

    fn index(&self, index: BindingId) -> &Self::Output {
        &self.bindings[index]
    }
}

impl<'a> std::ops::Index<DefId> for ThirBodyBuilder<'a> {
    type Output = Def;

    fn index(&self, index: DefId) -> &Self::Output {
        &self.defs[index]
    }
}

fn convert_mutability(m: &ra_ap_hir::Mutability) -> Mutability {
    match m {
        ra_ap_hir::Mutability::Mut => Mutability::Mut,
        ra_ap_hir::Mutability::Shared => Mutability::Shared,
    }
}

fn convert_binary_op(op: ast::BinaryOp) -> boris_shared::BinaryOp {
    fn convert_arith_op(op: ast::ArithOp) -> ArithOp {
        match op {
            ast::ArithOp::Add => ArithOp::Add,
            ast::ArithOp::Mul => ArithOp::Mul,
            ast::ArithOp::Sub => ArithOp::Sub,
            ast::ArithOp::Div => ArithOp::Div,
            ast::ArithOp::Rem => ArithOp::Rem,
            ast::ArithOp::Shl => ArithOp::Shl,
            ast::ArithOp::Shr => ArithOp::Shr,
            ast::ArithOp::BitXor => ArithOp::BitXor,
            ast::ArithOp::BitOr => ArithOp::BitOr,
            ast::ArithOp::BitAnd => ArithOp::BitAnd,
        }
    }
    match op {
        ast::BinaryOp::LogicOp(op) => BinaryOp::LogicOp(match op {
            ast::LogicOp::And => LogicOp::And,
            ast::LogicOp::Or => LogicOp::Or,
        }),
        ast::BinaryOp::ArithOp(op) => BinaryOp::ArithOp(convert_arith_op(op)),
        ast::BinaryOp::CmpOp(op) => BinaryOp::CmpOp(match op {
            ast::CmpOp::Eq { negated } => CmpOp::Eq { negated },
            ast::CmpOp::Ord { ordering, strict } => CmpOp::Ord {
                ordering: match ordering {
                    ast::Ordering::Less => Ordering::Less,
                    ast::Ordering::Greater => Ordering::Greater,
                },
                strict,
            },
        }),
        ast::BinaryOp::Assignment { op } => BinaryOp::Assignment {
            op: op.map(convert_arith_op),
        },
    }
}

fn convert_unary_op(op: ast::UnaryOp) -> UnaryOp {
    match op {
        ast::UnaryOp::Deref => UnaryOp::Deref,
        ast::UnaryOp::Not => UnaryOp::Not,
        ast::UnaryOp::Neg => UnaryOp::Neg,
    }
}

fn convert_binding_annotation(annotation: hir::BindingAnnotation) -> Option<BindingAnnotation> {
    match annotation {
        hir::BindingAnnotation::Unannotated => None,
        hir::BindingAnnotation::Mutable => Some(BindingAnnotation::Mutable),
        hir::BindingAnnotation::Ref => Some(BindingAnnotation::Ref),
        hir::BindingAnnotation::RefMut => Some(BindingAnnotation::RefMut),
    }
}
