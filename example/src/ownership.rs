fn do_something(text: String) {}

fn log(a: String, b: String) {}

fn ownership() {
    let x = String::from("Hello world");

    let mine_now = x;

    do_something(x);

    {
        let cloned_value = mine_now.clone();

        println!("`cloned_value` dropped here.");
    }

    do_something(mine_now)
}
