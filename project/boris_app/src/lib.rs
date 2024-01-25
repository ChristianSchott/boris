use boris_analysis::{Analysis, Function, FunctionId, ProjectModule};
use boris_shared::{ExampleState, ThirBody};
use eframe::egui::{self};
use egui::{
    ahash::{HashMap, RandomState},
    text::{LayoutJob, TextWrapping},
    Color32, FontId, TextEdit, Ui,
};

use std::{
    sync::mpsc,
    thread::{self, JoinHandle},
    time::Duration,
};

pub enum UserMessage {
    Load(String),
    AnalyzeFn(FunctionId),
    UpdateFn(FunctionId),
    Exit,
}

pub enum AnalysisResult {
    Data((FunctionId, ThirBody, Option<String>)),
    ProjectStructure(Box<[ProjectModule]>),
    Error(String),
}

pub struct AnalysisThread {
    rx: mpsc::Receiver<UserMessage>,
    tx: mpsc::Sender<AnalysisResult>,
    analysis: Option<Analysis>,
    ctx: Option<egui::Context>,
}
impl AnalysisThread {
    pub fn new(
        rx: mpsc::Receiver<UserMessage>,
        tx: mpsc::Sender<AnalysisResult>,
        ctx: Option<egui::Context>,
    ) -> Self {
        Self {
            analysis: None,
            rx,
            tx,
            ctx,
        }
    }

    fn main_loop(&mut self) -> Result<(), ()> {
        if let Ok(usr_msg) = self.rx.recv_timeout(Duration::from_millis(500)) {
            let response = match usr_msg {
                UserMessage::Load(path) => self.load_cargo_project(&path),
                UserMessage::AnalyzeFn(id) => self.analyze_fn(id),
                UserMessage::UpdateFn(id) => self.update_fn(id),
                UserMessage::Exit => return Err(()),
            };
            match self.tx.send(response) {
                Err(err) => println!("AnalysisThread send error: {}", err),
                _ => (),
            };
            if let Some(ctx) = &self.ctx {
                ctx.request_repaint();
            }
        }
        Ok(())
    }

    fn load_cargo_project(&mut self, path: &str) -> AnalysisResult {
        let path = match std::path::Path::new(path).canonicalize() {
            Ok(path) => path,
            Err(e) => return AnalysisResult::Error(e.to_string()),
        };
        match Analysis::from_cargo_project(&path) {
            Ok(a) => {
                self.analysis.replace(a);
                AnalysisResult::ProjectStructure(self.analysis.as_ref().unwrap().files())
            }
            Err(e) => AnalysisResult::Error(e.to_string()),
        }
    }

    fn analyze_fn(&self, function_id: FunctionId) -> AnalysisResult {
        let Some(analysis) = &self.analysis else {
            return AnalysisResult::Error(String::from("No open cargo project."));
        };
        let body = analysis.thir_body(function_id);
        body.map(|body| {
            AnalysisResult::Data((function_id, body, analysis.function_source(function_id)))
        })
        .unwrap_or_else(|| AnalysisResult::Error(String::from("Analysis failed!")))
    }

    fn update_fn(&mut self, function_id: FunctionId) -> AnalysisResult {
        let Some(analysis) = &mut self.analysis else {
            return AnalysisResult::Error(String::from("No open cargo project."));
        };
        analysis.reload(function_id);
        self.analyze_fn(function_id)
    }
}

enum AppMode {
    Done,
    Waiting,
    Err(String),
}

struct BodyDrawer {
    body: ThirBody,
    selected_def: Option<boris_shared::DefId>,
    source_code: Option<String>,
}

impl BodyDrawer {
    fn new(ctx: &egui::Context, body: ThirBody, source_code: Option<String>) -> Self {
        BodyDrawer {
            body,
            selected_def: None,
            source_code,
        }
    }

    const EXPORT_ROOT_DIR: &'static str = "./exports";

    fn export(&self) -> Result<String, String> {
        let state = ExampleState {
            body: self.body.clone(),
            selected: self.selected_def,
        };
        let json = serde_json::to_string(&state).map_err(|e| e.to_string())?;
        std::fs::create_dir_all(Self::EXPORT_ROOT_DIR).map_err(|e| e.to_string())?;
        let path = format!(
            "{}/fn_{}_{:#x}.boris",
            Self::EXPORT_ROOT_DIR,
            self.body.name,
            RandomState::new().hash_one(&self.body.name)
        );
        std::fs::write(&path, json).map_err(|e| e.to_string())?;
        Ok(path)
    }
}

pub struct MirVisApp {
    sender: mpsc::Sender<UserMessage>,
    receiver: mpsc::Receiver<AnalysisResult>,
    mode: AppMode,

    join_handle: Option<thread::JoinHandle<()>>,
    project_path: String,
    project_files: Box<[ProjectModule]>,

    selected_fn: Option<FunctionId>,
    fn_drawers: HashMap<FunctionId, BodyDrawer>,

    fn_filter: String,
}

impl MirVisApp {
    pub fn create(cc: &eframe::CreationContext<'_>) -> Self {
        let (tx, rx) = mpsc::channel::<UserMessage>();
        let (ty, ry) = mpsc::channel::<AnalysisResult>();
        let mut analysis = AnalysisThread::new(rx, ty, Some(cc.egui_ctx.clone()));

        let handle = thread::spawn(move || while let Ok(_) = analysis.main_loop() {});
        Self::new(cc, ry, tx, Some(handle))
    }

    pub fn new(
        cc: &eframe::CreationContext<'_>,
        ry: mpsc::Receiver<AnalysisResult>,
        tx: mpsc::Sender<UserMessage>,
        join_handle: Option<JoinHandle<()>>,
    ) -> Self {
        // String::from("C:\\Users\\Chris\\Documents\\Git\\rust\\playground")
        Self {
            sender: tx,
            receiver: ry,
            mode: AppMode::Done,
            join_handle,
            project_path: Default::default(),
            project_files: Default::default(),
            fn_filter: String::new(),
            selected_fn: None,
            fn_drawers: Default::default(),
        }
    }

    pub fn send(&mut self, message: UserMessage) {
        match self.sender.send(message) {
            Err(err) => println!("Send error! {}", err),
            _ => self.mode = AppMode::Waiting,
        }
    }

    fn receive_analysis_results(&mut self, ctx: &egui::Context) {
        for result in self.receiver.try_iter() {
            match result {
                AnalysisResult::Data((id, body, source)) => {
                    self.fn_drawers
                        .insert(id, BodyDrawer::new(ctx, body, source));
                }
                AnalysisResult::ProjectStructure(files) => self.project_files = files,
                AnalysisResult::Error(e) => {
                    self.mode = AppMode::Err(e);
                    break;
                }
            }
            self.mode = AppMode::Done;
        }
    }
}

impl eframe::App for MirVisApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        self.receive_analysis_results(ctx);

        egui::TopBottomPanel::top("top_panel")
            .resizable(false)
            .show(ctx, |ui| {
                ui.horizontal(|ui| {
                    ui.add(
                        TextEdit::singleline(&mut self.project_path).hint_text("project path.."),
                    );

                    if ui.button("Load cargo").clicked() {
                        self.project_files = Default::default();
                        self.fn_drawers.clear();
                        self.send(UserMessage::Load(self.project_path.clone()));
                    }
                    match &self.mode {
                        AppMode::Done => (),
                        AppMode::Waiting => {
                            ui.spinner();
                        }
                        AppMode::Err(err) => {
                            ui.label(err);
                        }
                    }

                    if let Some(fn_drawer) =
                        self.selected_fn.and_then(|id| self.fn_drawers.get(&id))
                    {
                        ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                            if ui.button("Export").clicked() {
                                if let Err(e) = fn_drawer.export() {
                                    self.mode = AppMode::Err(e);
                                }
                            }

                            if ui.button("+").clicked() {
                                ctx.set_zoom_factor(ctx.zoom_factor() + 0.2f32);
                            }

                            if ui.button("-").clicked() {
                                ctx.set_zoom_factor(ctx.zoom_factor() - 0.2f32);
                            }
                        });
                    }
                });
            });

        egui::SidePanel::left("files_panel")
            .resizable(true)
            .show(ctx, |ui| {
                let width = ui.available_width();
                ui.add(
                    TextEdit::singleline(&mut self.fn_filter)
                        .hint_text("filter..")
                        .desired_width(width),
                );

                egui::ScrollArea::vertical().show(ui, |ui| {
                    ui.separator();
                    fn draw_fn(ui: &mut Ui, func: &Function, filter: &str) -> Option<FunctionId> {
                        let clicked = if func.sig.contains(filter) {
                            let mut job = LayoutJob::simple_singleline(
                                func.sig.clone(),
                                FontId::monospace(12f32),
                                Color32::TEMPORARY_COLOR,
                            );
                            job.wrap = TextWrapping::no_max_width();
                            // Link::new(job)
                            ui.link(job).clicked().then_some(func.id)
                        } else {
                            None
                        };
                        if !func.local_fns.is_empty() {
                            ui.indent(func.id, |ui| {
                                func.local_fns.iter().fold(clicked, |state, local_fn| {
                                    draw_fn(ui, local_fn, filter).or(state)
                                })
                            })
                            .inner
                        } else {
                            clicked
                        }
                    }

                    fn draw_mod(
                        ui: &mut Ui,
                        module: &ProjectModule,
                        filter: &str,
                    ) -> Option<FunctionId> {
                        let mut job = LayoutJob::simple_singleline(
                            module.name.clone(),
                            FontId::monospace(12f32),
                            Color32::DARK_GRAY,
                        );
                        job.wrap = TextWrapping::no_max_width();
                        ui.collapsing(job, |ui| {
                            let clicked =
                                module.child_modules.iter().fold(None, |state, child_mod| {
                                    draw_mod(ui, child_mod, filter).or(state)
                                });

                            module
                                .functions
                                .iter()
                                .fold(clicked, |state, func| draw_fn(ui, func, filter).or(state))
                        })
                        .body_returned
                        .flatten()
                    }

                    let fn_clicked = self.project_files.iter().fold(None, |state, proj_crate| {
                        draw_mod(ui, &proj_crate, &self.fn_filter).or(state)
                    });

                    if let Some(selected) = fn_clicked {
                        self.selected_fn = Some(selected);
                        if self.fn_drawers.get(&selected).is_none() {
                            self.send(UserMessage::AnalyzeFn(selected));
                        }
                    }
                });
            });

        egui::SidePanel::right("code_editor")
            .resizable(true)
            .show(ctx, |ui| {
                ui.horizontal(|ui| {
                    ui.label("Source Code");
                    ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                        if ui.button("Reload").clicked() {
                            if let Some((id, _)) = self.selected_fn.and_then(|id| {
                                self.fn_drawers
                                    .get_mut(&id)
                                    .map(|d| (id, d.source_code.clone()))
                            }) {
                                self.send(UserMessage::UpdateFn(id));
                            }
                        }
                    });
                });

                egui::ScrollArea::both().show(ui, |ui| {
                    ui.separator();

                    if let Some(fn_drawer) =
                        self.selected_fn.and_then(|id| self.fn_drawers.get_mut(&id))
                    {
                        egui::ScrollArea::both().show(ui, |ui| {
                            let mut layouter = |ui: &egui::Ui, string: &str, _: f32| {
                                let layout_job = egui_extras::syntax_highlighting::highlight(
                                    ui.ctx(),
                                    &egui_extras::syntax_highlighting::CodeTheme::light(),
                                    string,
                                    "rs",
                                );
                                ui.fonts(|f| f.layout_job(layout_job))
                            };
                            // FIXME: the editing here does not actually do anything yet..
                            if let Some(source) = &mut fn_drawer.source_code {
                                ui.add(
                                    egui::TextEdit::multiline(source)
                                        .font(egui::TextStyle::Monospace) // for cursor height
                                        .code_editor()
                                        .lock_focus(true)
                                        .desired_width(f32::INFINITY)
                                        .layouter(&mut layouter),
                                );
                            } else {
                                ui.label("Source not available.");
                            }
                        });
                    }
                });
            });

        egui::CentralPanel::default().show(ctx, |ui| {
            egui::ScrollArea::both().show(ui, |ui| {
                if let Some(fn_drawer) =
                    self.selected_fn.and_then(|id| self.fn_drawers.get_mut(&id))
                {
                    boris_renderer::boris_view(
                        ctx,
                        ui,
                        &fn_drawer.body,
                        &mut fn_drawer.selected_def,
                    );
                }
            });
        });
    }

    fn on_exit(&mut self, _gl: Option<&eframe::glow::Context>) {
        self.sender.send(UserMessage::Exit).unwrap();
        self.join_handle.take().map(|handle| handle.join());
    }
}
