# BORIS - A BORrow vISualizer for Rust programs

This tool tries to visualize Rust's memory management, especially ownership transfer and borrows.
Aiming to make these concepts easier to grasp for beginners, and experienced programmers switching from other languages.

This project is part of my master's thesis at the Julius-Maximilians-University Würzburg, so the main focus is currently on finishing the thesis, not adding more features and fixing bugs ( feel free to do so, though :) )

For now it is a standalone program, but IDE integration may be something to look into for the future.

<iframe src="https://christianschott.github.io/boris-viewer/#ownership" width=100% height="250"></iframe>

## Limitations

- no borrow checker (no dependency unstable rust compiler hooks, or [polonius](https://github.com/rust-lang/polonius)).
  - no (/limited) error visualizations. However, the visualizations should still be useful while debugging borrow checker errors.
- complex lifetime annotations: rust analyzer does not lower lifetime annotations properly yet, meaning that any `struct test<'a, 'b> {}` will be treated as `struct test<'a, 'a> {}`
- `async`
- `unsafe` (interior mutability, inline assembly, etc.)
- bugs
- this was my first rust project, so coding style is probably suboptimal in many cases :)

## Crates

- `boris_shared`: data structures shared between the backend analysis, and rendering code
- `boris_analysis`: the core analysis code, depending on rust analyzer
- `boris_renderer`: code for rendering the analysis results
- `boris_app`: a standalone app, combining the analysis backend with a very basic frontend window
- `boris_viewer`: a WASM compatible frontend, for embedding into websites (without the analysis backend)
- `boris_exporter`: an internal tool for exporting/serializing analysis outputs, and creating graphics for the thesis

## Compilation

App:

- `cargo run -p boris_app --release` to run the main application

WASM Viewer:

- run `trunk serve` in the `boris_viewer` folder for running the web viewer application locally. More information about deploying can be found [here](https://github.com/emilk/eframe_template#web-locally).
  - the viewer directly embeds pre-analysed function bodies from the `./example/export/bodies/` folder (see `./project/boris_viewer/examples.rs`)
  - access examples via `url/#example_name` (e.g., https://christianschott.github.io/boris-viewer/#ownership)

## Credits

It is based on the powerful [rust-analyzer](https://github.com/rust-lang/rust-analyzer) crate, making this whole project even possible.
A special shoutout to [@HKalbasi](https://github.com/HKalbasi) for his recent work on adding [MIR](https://github.com/rust-lang/rust-analyzer/pull/14040) lowering to rust-analyzer, which was essential to this project, and of course the whole RA team.

For the rendering it utilizes [egui](https://github.com/emilk/egui), as it provided a very fast and simple way for drawing to the screen.

Some obvious inspirations:

- [RustViz](https://github.com/rustviz/rustviz)
- [Graphical depiction of ownership and borrowing in Rust](https://rufflewind.com/2017-02-15/rust-move-copy-borrow)
- [Think Spatially to Grok Lifetimes](https://www.justanotherdot.com/posts/think-spatially-to-grok-lifetimes.html)
- [Rust Lifetime Visualization Ideas](https://blog.adamant-lang.org/2019/rust-lifetime-visualization-ideas/)
- [Flowistry](https://github.com/willcrichton/flowistry/)
