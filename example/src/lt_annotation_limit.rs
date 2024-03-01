struct Container<'a, 'b> {
    a: &'a str,
    b: &'b str,
}

fn lt_annotations() {
    let hello = String::from("Hello");
    let world = String::from("World");

    let container = Container {
        a: &hello,
        b: &world,
    };

    let a_ref = container.a;
    println!("{a_ref}");
}
