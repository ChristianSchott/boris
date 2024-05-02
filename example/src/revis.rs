fn binding_move(x: [String; 4]) -> &'static [String; 4] {
    match x {
        a @ [.., _] => (),
        _ => (),
    }
    &x
}
