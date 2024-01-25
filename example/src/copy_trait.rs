fn log_values(a: i32, b: i32, c: i32) {}

fn primitive_test() {
    let number: i32 = 42;

    let other: i32 = number;

    let sum: i32 = other + number;

    log_values(number, sum, 7);
}
