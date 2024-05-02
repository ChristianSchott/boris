fn main() {
    let mut x = 42;
    x = {
        println!("calculating..");
        x + 1 // refers to the initial value of x
    };
}
