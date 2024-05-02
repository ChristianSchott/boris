fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn complex_arg(msg: &str) {
    let c = add(if msg.starts_with("Hello") { 1 } else { 2 }, 3);
    println!("{c}");
}
