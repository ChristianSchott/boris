fn closure_capture_ref() {
    let mut x = 0;
    let mut y = 0;

    let mut closure = || {
        x += 1;
        y += x;
    };

    closure();

    println!("x: {x}; y: {y}");
}
