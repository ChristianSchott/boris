const condition: bool = false;

fn main() {
    let s = String::from("Hello");
    if condition {
        drop(s);
    } else {
        println!("{s}");
    }
}
