#![warn(clippy::all, rust_2018_idioms)]

mod app;
pub use app::TemplateApp;
mod examples;
pub use examples::example_from_name;
