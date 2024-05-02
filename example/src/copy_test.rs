fn main() {
    let mut x = 42;
    let y = x;
    let ref_mut_x = &mut x;
    *ref_mut_x = 1337;
}
