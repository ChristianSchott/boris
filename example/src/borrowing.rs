fn borrow_string(s: &String) {}

fn modify_string(s: &mut String) {}

fn borrowing() {
    let mut owned_string = String::from("Hello");

    let borrow_a = &owned_string;
    let borrow_b = &owned_string;
    borrow_string(&owned_string);

    borrow_string(borrow_a);

    let mutable_borrow = &mut owned_string;

    modify_string(&mut owned_string);

    modify_string(mutable_borrow);
}
