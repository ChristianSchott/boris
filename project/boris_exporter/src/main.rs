use std::path::PathBuf;

use boris_analysis::{Analysis, ProjectModule};
use boris_shared::ExampleState;
use eframe::Theme;

mod capture;

#[derive(Debug)]
enum ErrorKind {
    FnNotFound,
    AnalysisFailed,
    SerializationFailed,
    ReadFailed,
    WriteFailed,
}

#[derive(Clone)]
struct Item {
    module: String,
    func: String,
    select: Option<String>,
}

impl Item {
    fn new(module: &str, func: &str, selected: Option<&str>) -> Self {
        Self {
            module: module.into(),
            func: func.into(),
            select: selected.map(|name| name.into()),
        }
    }
}

fn main() -> Result<(), ErrorKind> {
    let survey_examples = [
        Item::new("ownership", "ownership", Some("x")),
        Item::new("copy", "fibonacci", Some("n")),
        Item::new("mutability", "mutability", Some("sum")),
        Item::new("borrowing", "borrowing", Some("owned_string")),
        Item::new("higher_order_fn", "higher_order_functions_example", None),
    ];

    let export_items = survey_examples.clone();

    let capture_items = survey_examples.clone();

    let path_str = format!("{}\\..\\..\\example\\", env!("CARGO_MANIFEST_DIR"));
    let project_path = std::path::Path::new(&path_str)
        .canonicalize()
        .map_err(|_| ErrorKind::ReadFailed)?;

    let analysis = Analysis::from_cargo_project(&project_path).map_err(|e| {
        println!("{e}");
        ErrorKind::ReadFailed
    })?;
    println!("Loaded '{}'", project_path.display());

    export_functions(&analysis, &export_items, &project_path)?;
    capture_functions(&analysis, &capture_items, &project_path)?;

    Ok(())
}

// fn example_path(name: &str) -> String {
//     format!("{}\\examples\\{}.rs", env!("CARGO_MANIFEST_DIR"), name)
// }

// fn load_example(name: &str) -> Result<String, ErrorKind> {
//     let load_path = format!("{}\\examples\\{}.rs", env!("CARGO_MANIFEST_DIR"), name);
//     String::from_utf8(std::fs::read(load_path).map_err(|_| ErrorKind::ReadFailed)?)
//         .map_err(|_| ErrorKind::ReadFailed)
// }

fn export_functions(analysis: &Analysis, items: &[Item], path: &PathBuf) -> Result<(), ErrorKind> {
    for item in items {
        let example = analyze(analysis, item)?;
        let export_path = format!(
            "{}\\export\\bodies\\{}.json",
            path.to_str().unwrap_or(""),
            item.module,
        );
        let json = serde_json::to_string(&example).map_err(|_| ErrorKind::SerializationFailed)?;
        std::fs::write(&export_path, json).map_err(|_| ErrorKind::WriteFailed)?;
    }
    Ok(())
}

fn capture_functions(analysis: &Analysis, items: &[Item], path: &PathBuf) -> Result<(), ErrorKind> {
    let mut states = vec![];
    for item in items {
        // let contents = example_path(&file)?;
        let example = analyze(analysis, item)?;
        states.push((item.module.clone(), example));
    }
    let native_options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default().with_fullscreen(true),
        default_theme: Theme::Light,
        follow_system_theme: false,
        ..Default::default()
    };
    let export_dir = format!("{}\\export\\imgs\\", path.to_str().unwrap_or(""));
    eframe::run_native(
        "Boris",
        native_options,
        Box::new(|cc| Box::new(capture::CaptureApp::new(cc, states, export_dir))),
    )
    .map_err(|_| ErrorKind::WriteFailed)
}

fn analyze(analysis: &Analysis, item: &Item) -> Result<ExampleState, ErrorKind> {
    fn find_module<'a>(modules: &'a [ProjectModule], item: &Item) -> Option<&'a ProjectModule> {
        if let Some(module) = modules.iter().find(|module| module.name == item.module) {
            Some(module)
        } else {
            for module in modules {
                if let Some(child_mod) = find_module(&module.child_modules, item) {
                    return Some(child_mod);
                }
            }
            None
        }
    }

    let modules = analysis.files();
    let module = find_module(&modules, item).ok_or(ErrorKind::FnNotFound)?;
    let func_id = module
        .functions
        .iter()
        .find_map(|func| func.sig.contains(&item.func).then_some(func.id))
        .ok_or(ErrorKind::FnNotFound)?;

    let body = analysis
        .thir_body(func_id)
        .ok_or(ErrorKind::AnalysisFailed)?;

    let selected = item.select.as_ref().and_then(|select| {
        body.def_graph
            .iter()
            .find_map(|(def, node)| match node.kind {
                boris_shared::NodeKind::Source { binding, .. } => {
                    (&body.bindings[binding].name == select).then_some(def)
                }
                _ => None,
            })
    });

    Ok(ExampleState { body, selected })
}
