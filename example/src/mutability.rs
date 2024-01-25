fn mutability() {
    let immutable = String::from("Hello");
    immutable.push_str(" world?");

    let mut mutable = immutable;
    mutable.push_str(" world!");
}
