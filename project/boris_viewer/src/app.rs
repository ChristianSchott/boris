use boris_shared::{BirBody, DefId, ExampleState};
use itertools::Itertools;

#[derive(Default)]
pub struct TemplateApp {
    body: Option<BirBody>,
    selected_defs: Vec<DefId>,
}

impl TemplateApp {
    pub fn new(cc: &eframe::CreationContext<'_>, state: Option<ExampleState>) -> Self {
        if let Some(state) = state {
            TemplateApp {
                body: Some(state.body),
                selected_defs: state.selected.into_iter().collect(),
                ..Default::default()
            }
        } else {
            TemplateApp::default()
        }
    }
}

impl eframe::App for TemplateApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            if let Some(body) = self.body.as_ref() {
                boris_renderer::boris_view(ctx, ui, body, &mut self.selected_defs);
            }
        });
    }
}
