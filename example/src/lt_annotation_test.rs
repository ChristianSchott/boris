fn main(z: i32) {
    let mut x = String::from("Hello world!");

    let y = 42;

    if y != z {
        println!("{}", x);
    } else {
        x = x.to_lowercase();
    }

    drop(x);
}
