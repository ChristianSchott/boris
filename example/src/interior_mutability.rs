use std::cell::RefCell;

fn interior_mutability() {
    let ref_cell = RefCell::new(5);
    let shared_ref = ref_cell.borrow();
    *ref_cell.borrow_mut() = 42;
    println!("{}", shared_ref);
}
