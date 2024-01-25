use eframe::Theme;

mod lib;

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    std::env::set_var("RUST_BACKTRACE", "1");
    env_logger::init(); // Log to stderr (if you run with `RUST_LOG=debug`).

    let native_options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_inner_size([640.0, 420.0])
            .with_min_inner_size([420.0, 300.0]),
        default_theme: Theme::Light,
        follow_system_theme: false,
        ..Default::default()
    };
    eframe::run_native(
        "Boris",
        native_options,
        Box::new(|cc| {
            let mut app = Box::new(lib::MirVisApp::create(cc));
            // TODO: remove this
            app.send(lib::UserMessage::Load(String::from(
                "C:\\Users\\Chris\\Documents\\Git\\rust\\playground",
            )));
            app
        }),
    )
    .ok();
}
