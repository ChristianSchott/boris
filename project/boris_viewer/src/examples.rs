use boris_shared::ExampleState;
use include_dir::Dir;

// directly include the example files in the compilation, so we don't have to deal with loading them via WASM somehow..
static EXAMPLES_DIR: Dir<'_> =
    include_dir::include_dir!("$CARGO_MANIFEST_DIR/../../example/export/bodies/");

fn example_from_string(file: &str) -> Option<ExampleState> {
    serde_json::from_str(file).ok()
}

pub fn example_from_name(name: &str) -> Option<ExampleState> {
    EXAMPLES_DIR
        .files()
        .find_map(|file| {
            file.path()
                .file_stem()
                .and_then(|stem| stem.to_str())
                .and_then(|stem| (stem == name).then_some(file.contents()))
                .and_then(|contents| std::str::from_utf8(contents).ok())
        })
        .and_then(|contents| example_from_string(contents))
}
