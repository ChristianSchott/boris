use boris_shared::{BirBody, DefId, ExampleState};
use egui::Rect;

pub struct CaptureApp {
    directory: String,
    examples: Vec<(String, ExampleState)>,
    drawer: Option<(String, BirBody, Vec<DefId>)>,
    rect: Rect,
}

impl CaptureApp {
    pub fn new(
        cc: &eframe::CreationContext<'_>,
        examples: Vec<(String, ExampleState)>,
        directory: String,
    ) -> Self {
        cc.egui_ctx.set_zoom_factor(1.5f32);
        CaptureApp {
            directory,
            examples,
            drawer: None,
            rect: Rect::NOTHING,
        }
    }
}

impl eframe::App for CaptureApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        if !self.drawer.is_some() {
            if let Some((name, state)) = self.examples.pop() {
                self.drawer = Some((
                    name,
                    state.body.clone(),
                    // boris_renderer::main_body_renderer(ctx, &state.body),
                    state.selected.into_iter().collect(),
                ));
                ctx.send_viewport_cmd(egui::ViewportCommand::Screenshot);
            } else {
                ctx.send_viewport_cmd(egui::ViewportCommand::Close);
            }
        }

        egui::CentralPanel::default().show(ctx, |ui| {
            if let Some((_, body, selected)) = self.drawer.as_mut() {
                self.rect = boris_renderer::boris_view(ctx, ui, body, selected);
            }
            ui.input(|i| {
                for event in &i.raw.events {
                    if let egui::Event::Screenshot { image, .. } = event {
                        if let Some((name, _, _)) = &self.drawer {
                            let path = format!("{}{}.png", self.directory, name);

                            let pixels_per_point = i.pixels_per_point();
                            let cropped = image.region(&self.rect, Some(pixels_per_point));
                            image::save_buffer(
                                &path,
                                cropped.as_raw(),
                                cropped.width() as u32,
                                cropped.height() as u32,
                                image::ColorType::Rgba8,
                            )
                            .unwrap();
                            println!("Export: '{}'", path);
                        }

                        self.drawer.take(); // ready for screenshot
                    }
                }
            });
        });
    }
}
