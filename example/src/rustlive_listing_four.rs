// listing 4
// Simple Explanation of Complex Lifetime Errors in Rust
// Bachelor Thesis
// David Blaser
fn main() {
    let mut x = 4;
    let y = &x;
    let d = &x;
    let y2 = move || {
        println!("{}", y);
    };
    let y3 = y2;
    let e = &d;
    let mut g = 5;
    let z = bar(&y3);
    let f = &mut g;
    let w = foobar(&z);
    let mut a = 32;
    let b = 42;

    let s = &w;
    let r = s;

    x = 5;
    *f = 42;
    take(g);
    take(w);
}

fn foo<T>(p: T) -> T {
    p
}

fn bar<T>(p: T) -> T {
    p
}
fn foobar<T>(p: T) -> T {
    p
}
fn take<T>(p: T) {
    unimplemented!()
}
