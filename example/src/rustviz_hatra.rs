fn main() {
    let mut s = String::from("hello");

    let r1 = &s;
    let r2 = &s;
    assert!(compare_strings(r1, r2));

    let r3 = &mut s;
    clear_string(r3)
}

fn compare_strings(a: &str, b: &str) -> bool {
    true
}

fn clear_string(a: &mut String) {}
