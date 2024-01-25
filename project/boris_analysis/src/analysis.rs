use ide_db::base_db::salsa::ParallelDatabase;
use ide_db::symbol_index::SymbolsDatabase;
use ide_db::RootDatabase;
use itertools::Itertools;
use la_arena::Idx;
use paths::AbsPath;
use proc_macro_api::ProcMacroServer;
use ra_ap_hir_def::db::InternDatabase;
use ra_ap_hir_def::nameres::{ModuleData, ModuleOrigin};
use ra_ap_hir_def::src::HasSource;

use ra_ap_hir_ty::db::HirDatabase;
use std::str;
use triomphe::Arc;
use vfs::file_set::FileSet;

use hir::db::DefDatabase;
use hir::{CfgOptions, Change, DefMap, DefWithBody, HirDisplay, InRealFile, Semantics, TypeRef};
use ide::{
    AnalysisHost, Cancelled, CrateGraph, Edition, FileId, SourceRoot, StructureNodeKind, SymbolKind,
};
use ide_db::base_db::{
    CrateName, CrateOrigin, Env, FileLoader, SourceDatabase, SourceDatabaseExt, Upcast,
};
use load_cargo::LoadCargoConfig;
use project_model::{target_data_layout, CargoConfig, ProjectManifest, ProjectWorkspace};
pub use ra_ap_hir_def::FunctionId;
use syntax::{algo::find_node_at_offset, ast, AstNode};
use vfs::Vfs;

use ra_ap_hir as hir;
use ra_ap_ide as ide;
use ra_ap_ide_db as ide_db;
use ra_ap_load_cargo as load_cargo;
use ra_ap_paths as paths;
use ra_ap_proc_macro_api as proc_macro_api;
use ra_ap_project_model as project_model;
use ra_ap_syntax as syntax;
use ra_ap_vfs as vfs;

pub use vfs::VfsPath;

pub struct Analysis {
    pub host: AnalysisHost,
    pub vfs: Vfs,
    pub proc_macro: Option<ProcMacroServer>,
}

pub struct Function {
    pub sig: String,
    pub id: FunctionId,
    pub local_fns: Vec<Function>,
}

pub struct ProjectModule {
    pub name: String,
    pub functions: Vec<Function>,
    pub child_modules: Vec<ProjectModule>,
}

impl Analysis {
    // taken from ra_ap_ide::Analysis to get access to the analysis host
    // FIXME: not actually used..
    pub fn from_single_file(data: &str) -> Self {
        let mut host = AnalysisHost::default();
        let file_id = FileId::from_raw(0);
        let mut file_set = FileSet::default();
        file_set.insert(file_id, VfsPath::new_virtual_path("/main.rs".to_string()));
        let source_root = SourceRoot::new_local(file_set);

        let mut change = Change::new();
        change.set_roots(vec![source_root]);
        let mut crate_graph = CrateGraph::default();
        crate_graph.add_crate_root(
            file_id,
            Edition::CURRENT,
            Some(CrateName::normalize_dashes("root").into()),
            None,
            CfgOptions::default(),
            None,
            Env::default(),
            false,
            CrateOrigin::Local {
                repo: None,
                name: Some("tmp".into()),
            },
            match target_data_layout::get(None, None, &Default::default()).as_ref() {
                Ok(it) => Ok(Arc::from(it.as_str())),
                Err(it) => Err(Arc::from(it.to_string().as_str())),
            },
            None,
        );
        change.change_file(file_id, Some(Arc::from(data)));
        change.set_crate_graph(crate_graph);
        host.apply_change(change);
        Self {
            host,
            vfs: Vfs::default(),
            proc_macro: None,
        }
    }

    pub fn from_cargo_project(path: &std::path::Path) -> Result<Analysis, anyhow::Error> {
        let manifest = ProjectManifest::discover_single(AbsPath::assert(&path))?;
        let cargo_config = CargoConfig {
            sysroot: Some(project_model::RustLibSource::Discover),
            rustc_source: Some(project_model::RustLibSource::Discover),
            ..Default::default()
        };
        let ws = ProjectWorkspace::load(manifest, &cargo_config, &|_| {})?;
        let load_cargo_config = LoadCargoConfig {
            load_out_dirs_from_check: false,
            with_proc_macro_server: load_cargo::ProcMacroServerChoice::Sysroot,
            prefill_caches: false,
        };
        // TODO: load_workspace with watcher on target file
        let (host, vfs, proc_macro) =
            load_cargo::load_workspace(ws, &Default::default(), &load_cargo_config)?;
        Ok(Self {
            host,
            vfs,
            proc_macro,
        })
    }

    fn fn_sig(id: FunctionId, db: &dyn HirDatabase) -> String {
        let data = db.function_data(id);
        let ty_to_string =
            |type_ref: &TypeRef| -> String { type_ref.display_truncated(db, None).to_string() };
        let visibility = match &data.visibility {
            ra_ap_hir_def::visibility::RawVisibility::Module(path, _) => {
                match &path.kind {
                    hir::PathKind::Super(0) => "", // self aka private
                    hir::PathKind::Super(_) => "pub(super) ",
                    hir::PathKind::Crate => "pub(crate) ",
                    _ => "",
                }
            }
            ra_ap_hir_def::visibility::RawVisibility::Public => "pub ",
        };
        let params = data
            .params
            .iter()
            .map(|param| ty_to_string(param))
            .join(", ");
        format!(
            "{}fn {}({}) -> {}",
            visibility,
            data.name.display(db.upcast()),
            params,
            ty_to_string(&data.ret_type)
        )
    }

    pub fn files(&self) -> Box<[ProjectModule]> {
        fn traverse_fn(id: FunctionId, db: &RootDatabase) -> Function {
            let mut local_fns = vec![];
            for (_, block_defs) in db.body(id.into()).blocks(db.upcast()) {
                for (_, data) in block_defs.modules() {
                    local_fns.extend(data.scope.declarations().filter_map(|def| match def {
                        ra_ap_hir_def::ModuleDefId::FunctionId(local_id) => {
                            Some(traverse_fn(local_id, db))
                        }
                        _ => None,
                    }));
                    for impl_id in data.scope.impls() {
                        local_fns.extend(db.impl_data(impl_id).items.iter().filter_map(|item| {
                            match item {
                                ra_ap_hir_def::AssocItemId::FunctionId(local_id) => {
                                    Some(traverse_fn(*local_id, db))
                                }
                                _ => None,
                            }
                        }));
                    }
                }
            }
            let sig = Analysis::fn_sig(id, db.upcast());
            Function { sig, id, local_fns }
        }

        fn traverse_module(
            id: Idx<ModuleData>,
            krate_defs: &DefMap,
            db: &RootDatabase,
        ) -> ProjectModule {
            let mut functions = vec![];

            let mut insert_fn = |func: FunctionId| {
                functions.push(traverse_fn(func, db));
            };

            for def in krate_defs[id].scope.declarations() {
                match def {
                    ra_ap_hir_def::ModuleDefId::FunctionId(fn_id) => {
                        insert_fn(fn_id);
                    }
                    _ => (),
                }
            }

            for impl_id in krate_defs[id].scope.impls() {
                for item in db.impl_data(impl_id).items.iter() {
                    match item {
                        ra_ap_hir_def::AssocItemId::FunctionId(impl_fn_id) => {
                            insert_fn(*impl_fn_id);
                        }
                        _ => (),
                    }
                }
            }

            ProjectModule {
                name: krate_defs
                    .module_id(id)
                    .name(db.upcast())
                    .map(|name| name.display(db.upcast()).to_string())
                    .unwrap_or_default(),
                functions,
                child_modules: krate_defs[id]
                    .children
                    .iter()
                    .map(|(_, child_id)| traverse_module(*child_id, krate_defs, db))
                    .collect(),
            }
        }

        match Cancelled::catch(|| {
            let mut crates = vec![];
            let db = self.host.raw_database().snapshot();
            for root in db.local_roots().iter() {
                for root_krate in db.source_root_crates(*root).iter() {
                    let name = db.crate_graph()[*root_krate]
                        .display_name
                        .as_ref()
                        .map(|name| name.to_string())
                        .unwrap_or_default();

                    let krate_defs = db.crate_def_map(*root_krate);

                    if let Some(root_mod) = krate_defs
                        .clone()
                        .modules()
                        .find(|(_, m)| matches!(m.origin, ModuleOrigin::CrateRoot { .. }))
                        .map(|(id, _)| id)
                    {
                        let mut root_module = traverse_module(root_mod, krate_defs.as_ref(), &db);
                        root_module.name = name; // the root_module is just the crate
                        crates.push(root_module);
                    }
                }
            }
            crates.into_boxed_slice()
        }) {
            Ok(modules) => modules,
            Err(err) => {
                println!("Cancelled! {}", err);
                Default::default()
            }
        }
    }

    pub fn find_fn_body_def(&self, target_file_id: FileId, fn_name: &str) -> Option<DefWithBody> {
        let nodes = self.host.analysis().file_structure(target_file_id).ok()?;
        let offset = nodes
            .iter()
            .filter(|&node| {
                matches!(
                    node.kind,
                    StructureNodeKind::SymbolKind(SymbolKind::Function) if node.label == fn_name
                )
            })
            .next()
            .map(|node| node.node_range.start())?;

        let sema = &Semantics::new(self.host.raw_database());
        let source_file = sema.parse(target_file_id);
        let item = find_node_at_offset::<ast::Item>(source_file.syntax(), offset).unwrap();
        Some(match item {
            ast::Item::Fn(it) => sema.to_def(&it).unwrap().into(),
            ast::Item::Const(it) => sema.to_def(&it).unwrap().into(),
            ast::Item::Static(it) => sema.to_def(&it).unwrap().into(),
            _ => return None,
        })
    }

    fn function_to_ast(&self, fn_def_id: FunctionId) -> Option<InRealFile<ast::Fn>> {
        let db = self.host.raw_database().snapshot();

        db.lookup_intern_function(fn_def_id)
            .source(db.upcast())
            .original_ast_node_rooted(db.upcast())
            .map(|node| node)
    }

    pub fn function_source(&self, fn_def_id: FunctionId) -> Option<String> {
        self.function_to_ast(fn_def_id)
            .map(|func| func.value.syntax().text().to_string())
    }

    pub fn reload(&mut self, fn_def_id: FunctionId) {
        if let Some(node) = self.function_to_ast(fn_def_id) {
            let path = self.vfs.file_path(node.file_id);
            if let Some(contents) = path.as_path().and_then(|path| std::fs::read(path).ok()) {
                self.vfs.set_file_contents(path, Some(contents));
            }
        }
        let mut analysis_change = Change::new();
        for file in self.vfs.take_changes() {
            let contents = SourceDatabaseExt::file_text(self.host.raw_database(), file.file_id);
            analysis_change.change_file(file.file_id, Some(contents.into()))
        }
        self.host.apply_change(analysis_change);
    }

    pub fn thir_body(&self, fn_def_id: FunctionId) -> Option<boris_shared::ThirBody> {
        let db = self.host.raw_database().snapshot();
        match Cancelled::catch(|| crate::builder::create_thir_body(fn_def_id, db.upcast())) {
            Ok(body) => Some(body),
            Err(err) => {
                println!("Cancelled! {}", err);
                None
            }
        }
    }
}
