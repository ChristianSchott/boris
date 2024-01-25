fn borrow_string(s: &String) {}

fn modify_string(s: &mut String) {}

fn borrowing() {
    println!("Multiple borrows to an immutable string.");
    {
        let owned_string = String::from("Hello");

        let borrow = &owned_string;
        borrow_string(&owned_string);
        borrow_string(borrow);
    }

    let mut mutable_string = String::from("World");

    if mutable_string.is_empty() {
        mutable_string.push_str("Hello there.");
    } else {
        println!("The string is not empty.");
        modify_string(&mut mutable_string);
    }

    println!("'{}'", mutable_string);
}
