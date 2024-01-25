use either::Either;
use la_arena::{Arena, ArenaMap, Idx};
use ra_ap_hir::{Adt, GenericDef};
use ra_ap_hir_def::{DefWithBodyId, FieldId, HasModule, TupleFieldId};
use ra_ap_hir_ty::{
    db::HirDatabase,
    mir::{
        LocalId, MirBody, Operand, Place, ProjectionElem, ProjectionStore, Rvalue, StatementKind,
        TerminatorKind,
    },
    Interner, Mutability, Ty, TyExt, TyKind, TypeFlags,
};
use ra_ap_ide::CrateId;

pub type MovePathId = Idx<MovePath>;
pub type PlaceElem = ProjectionElem<LocalId, Ty>;

#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum ProjectionKind {
    Deref,
    Field(Either<FieldId, TupleFieldId>),
    ClosureField(usize),
    Index,
    SubSlice,
}

impl From<&PlaceElem> for ProjectionKind {
    fn from(value: &PlaceElem) -> Self {
        match value {
            PlaceElem::Deref => ProjectionKind::Deref,
            PlaceElem::Field(id) => ProjectionKind::Field(*id),
            PlaceElem::ClosureField(index) => ProjectionKind::ClosureField(*index),
            PlaceElem::Index(_) | ProjectionElem::ConstantIndex { .. } => ProjectionKind::Index,
            PlaceElem::Subslice { .. } => ProjectionKind::SubSlice,
            _ => panic!("Unhandled projection elem {:?}", value),
        }
    }
}

#[derive(Clone, Debug)]
pub enum ParentKind {
    Local(LocalId),
    Path(MovePathId),
}

#[derive(Clone, Debug)]
pub enum RefInfo {
    Reference { mutable: bool },
    HasRef,
    NoRef,
}

#[derive(Clone, Debug)]
pub struct MovePath {
    pub parent: ParentKind,
    pub children: Vec<(ProjectionKind, MovePathId)>,
    pub is_copy: bool,
    pub ref_info: RefInfo,
}

impl MovePath {
    fn new(parent: ParentKind, ty: &Ty, owner: DefWithBodyId, db: &dyn HirDatabase) -> Self {
        MovePath {
            parent,
            children: Default::default(),
            is_copy: ty.clone().is_copy(db, owner),
            ref_info: match ty.kind(Interner) {
                TyKind::Ref(mutability, _, _) | TyKind::Raw(mutability, _) => RefInfo::Reference {
                    mutable: matches!(mutability, Mutability::Mut),
                },
                // TyKind::Adt(id, _) => ,// check if is lang_item owned box
                _ => {
                    if Self::has_ref(ty.kind(Interner), db) {
                        RefInfo::HasRef
                    } else {
                        RefInfo::NoRef
                    }
                }
            },
        }
    }

    pub fn has_ref(ty: &TyKind, db: &dyn HirDatabase) -> bool {
        match ty {
            TyKind::Ref(_, _, _) => true,
            TyKind::Tuple(_, subst) => subst
                .type_parameters(Interner)
                .any(|param| Self::has_ref(&param.kind(Interner), db)),
            TyKind::Array(ty, _) | TyKind::Slice(ty) => Self::has_ref(ty.kind(Interner), db),
            TyKind::Adt(adt_id, _) => {
                let def = GenericDef::from(Adt::from(adt_id.0));
                !def.lifetime_params(db).is_empty()
            }
            TyKind::Closure(id, subst) => {
                let (def, _) = db.lookup_intern_closure((*id).into());
                let infer = db.infer(def);
                let (captures, _) = infer.closure_info(id);
                // capture by ref, or captures a reference
                captures.iter().any(|cap| match cap.kind() {
                    ra_ap_hir_ty::CaptureKind::ByRef(_) => true,
                    ra_ap_hir_ty::CaptureKind::ByValue => {
                        Self::has_ref(&cap.ty(subst).kind(Interner), db)
                    }
                })
            }
            _ => ty.compute_flags(Interner).intersects(
                TypeFlags::HAS_RE_ERASED
                    | TypeFlags::HAS_RE_PLACEHOLDER
                    | TypeFlags::HAS_RE_INFER
                    | TypeFlags::HAS_RE_LATE_BOUND
                    | TypeFlags::HAS_FREE_REGIONS
                    | TypeFlags::HAS_FREE_LOCAL_REGIONS,
            ),
        }
    }

    pub fn find_child(&self, proj: &PlaceElem) -> Option<MovePathId> {
        let proj_kind = ProjectionKind::from(proj);
        self.children
            .iter()
            .find_map(|(child_proj, child_path)| (*child_proj == proj_kind).then(|| *child_path))
    }

    pub fn contains_lt(&self) -> bool {
        matches!(self.ref_info, RefInfo::HasRef | RefInfo::Reference { .. })
    }
}

#[derive(Debug)]
pub struct MoveData<'a> {
    db: &'a dyn HirDatabase,
    body: &'a MirBody,
    crate_id: CrateId,

    pub move_paths: Arena<MovePath>,
    pub locals: ArenaMap<LocalId, MovePathId>,
}

impl<'a> MoveData<'a> {
    pub fn local(&self, mut move_path: MovePathId) -> LocalId {
        loop {
            move_path = match self.move_paths[move_path].parent {
                ParentKind::Local(local) => {
                    break local;
                }
                ParentKind::Path(parent) => parent,
            };
        }
    }

    pub fn move_path_for(&self, local: LocalId) -> MovePathId {
        self.locals[local]
    }

    pub fn children(&self, move_path_id: MovePathId) -> &[(ProjectionKind, MovePathId)] {
        &self.move_paths[move_path_id].children
    }

    pub fn find_child(&self, move_path_id: MovePathId, proj: &PlaceElem) -> Option<MovePathId> {
        self.move_paths[move_path_id].find_child(proj)
    }

    pub fn for_each_child_path(&self, move_path_id: MovePathId, mut f: impl FnMut(MovePathId)) {
        let mut stack = vec![move_path_id];
        while let Some(top) = stack.pop() {
            f(top);
            stack.extend(self.children(top).iter().map(|(_, child_path)| child_path))
        }
    }

    fn projected_ty(&self, ty: Ty, proj: &PlaceElem) -> Ty {
        proj.projected_ty(
            ty,
            self.db,
            |c, subst, f| {
                let (def, _) = self.db.lookup_intern_closure(c.into());
                let infer = self.db.infer(def);
                let (captures, _) = infer.closure_info(&c);
                captures.get(f).expect("broken closure field").ty(subst)
            },
            self.crate_id,
        )
    }

    pub fn ty_after_adjustments(&self, ty: &Ty, projections: &[PlaceElem]) -> Ty {
        let mut ty = ty.clone();
        for proj in projections {
            ty = self.projected_ty(ty, proj);
        }
        ty
    }

    pub fn is_copy(&self, ty: &Ty, projections: &[PlaceElem]) -> bool {
        self.ty_after_adjustments(ty, projections)
            .is_copy(self.db, self.body.owner)
    }

    pub fn is_root(&self, move_path_id: MovePathId) -> bool {
        matches!(self[move_path_id].parent, ParentKind::Local(_))
    }

    pub fn place_info(&self, place: &Place) -> (bool, Option<bool>) {
        let mut ty = self.body.locals[place.local].ty.clone();
        let mut behind_mutable_ref = None;
        for proj in place.projection.lookup(&self.body.projection_store) {
            if matches!(proj, PlaceElem::Deref) {
                match ty.kind(Interner) {
                    TyKind::Ref(mutability, _, _) | TyKind::Raw(mutability, _) => {
                        behind_mutable_ref = Some(matches!(mutability, Mutability::Mut));
                    }
                    // TyKind::Adt(id, _) => ,// check if is lang_item owned box
                    _ => {
                        println!("Deref called on non-ref type. Probably a box.. TODO");
                        // just pretend like it is mutable for now..
                        behind_mutable_ref = Some(true);
                    }
                }
            }
            ty = self.projected_ty(ty.clone(), proj);
        }
        let is_copy = ty.is_copy(self.db, self.body.owner);
        (is_copy, behind_mutable_ref)
    }

    fn alloc_place(&mut self, place: &Place) {
        let mut ty = self.body.locals[place.local].ty.clone();
        let mut move_path = self.move_path_for(place.local);
        for projection in place.projection.lookup(&self.body.projection_store) {
            if matches!(projection, ProjectionElem::Deref) {
                break;
            }
            ty = self.projected_ty(ty.clone(), projection);
            if let Some(child_path) = self.find_child(move_path, projection) {
                move_path = child_path;
            } else {
                let child_path = self.move_paths.alloc(MovePath::new(
                    ParentKind::Path(move_path),
                    &ty,
                    self.body.owner,
                    self.db,
                ));
                self.move_paths[move_path]
                    .children
                    .push((projection.into(), child_path));
                move_path = child_path;
            }
        }
    }

    pub fn new(body: &'a MirBody, db: &'a dyn HirDatabase) -> MoveData<'a> {
        let module_id = body.owner.module(db.upcast());
        let crate_id = module_id.krate();

        // db.lang_item(crate_id, ra_ap_hir::LangItem::OwnedBox).unwrap().as_struct().unwrap()

        let mut move_paths = Arena::new();
        let locals: ArenaMap<_, _> = body
            .locals
            .iter()
            .map(|(id, local)| {
                let move_path = move_paths.alloc(MovePath::new(
                    ParentKind::Local(id),
                    &local.ty,
                    body.owner,
                    db,
                ));
                (id, move_path)
            })
            .collect();

        // for (local, mp) in locals.iter() {
        //     println!("{local:?}: is copy {}", move_paths[*mp].is_copy);
        // }

        let mut move_data = MoveData {
            db,
            body,
            crate_id,
            move_paths,
            locals,
        };

        Self::walk_places(body, |place, store| {
            move_data.alloc_place(place);
        });

        move_data
    }

    // stolen from mir.rs
    fn walk_places(body: &MirBody, mut f: impl FnMut(&Place, &ProjectionStore)) {
        fn for_operand(
            op: &Operand,
            f: &mut impl FnMut(&Place, &ProjectionStore),
            store: &ProjectionStore,
        ) {
            match op {
                Operand::Copy(p) | Operand::Move(p) => {
                    f(p, store);
                }
                Operand::Constant(_) | Operand::Static(_) => (),
            }
        }
        for (_, block) in body.basic_blocks.iter() {
            for statement in &block.statements {
                match &statement.kind {
                    StatementKind::Assign(p, r) => {
                        f(p, &body.projection_store);
                        match r {
                            Rvalue::ShallowInitBoxWithAlloc(_) => (),
                            Rvalue::ShallowInitBox(o, _)
                            | Rvalue::UnaryOp(_, o)
                            | Rvalue::Cast(_, o, _)
                            | Rvalue::Repeat(o, _)
                            | Rvalue::Use(o) => for_operand(o, &mut f, &body.projection_store),
                            Rvalue::CopyForDeref(p)
                            | Rvalue::Discriminant(p)
                            | Rvalue::Len(p)
                            | Rvalue::Ref(_, p) => f(p, &body.projection_store),
                            Rvalue::CheckedBinaryOp(_, o1, o2) => {
                                for_operand(o1, &mut f, &body.projection_store);
                                for_operand(o2, &mut f, &body.projection_store);
                            }
                            Rvalue::Aggregate(_, ops) => {
                                for op in ops.iter() {
                                    for_operand(op, &mut f, &body.projection_store);
                                }
                            }
                        }
                    }
                    StatementKind::FakeRead(p) | StatementKind::Deinit(p) => {
                        f(p, &body.projection_store)
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Nop => (),
                }
            }
            match &block.terminator {
                Some(x) => match &x.kind {
                    TerminatorKind::SwitchInt { discr, .. } => {
                        for_operand(discr, &mut f, &body.projection_store)
                    }
                    TerminatorKind::FalseEdge { .. }
                    | TerminatorKind::FalseUnwind { .. }
                    | TerminatorKind::Goto { .. }
                    | TerminatorKind::UnwindResume
                    | TerminatorKind::CoroutineDrop
                    | TerminatorKind::Abort
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable => (),
                    TerminatorKind::Drop { place, .. } => {
                        f(place, &body.projection_store);
                    }
                    TerminatorKind::DropAndReplace { place, value, .. } => {
                        f(place, &body.projection_store);
                        for_operand(value, &mut f, &body.projection_store);
                    }
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        for_operand(func, &mut f, &body.projection_store);
                        args.iter()
                            .for_each(|x| for_operand(x, &mut f, &body.projection_store));
                        f(destination, &body.projection_store);
                    }
                    TerminatorKind::Assert { cond, .. } => {
                        for_operand(cond, &mut f, &body.projection_store);
                    }
                    TerminatorKind::Yield {
                        value, resume_arg, ..
                    } => {
                        for_operand(value, &mut f, &body.projection_store);
                        f(resume_arg, &body.projection_store);
                    }
                },
                None => (),
            }
        }
    }
}

impl<'a> std::ops::Index<MovePathId> for MoveData<'a> {
    type Output = MovePath;

    fn index(&self, index: MovePathId) -> &Self::Output {
        &self.move_paths[index]
    }
}
