fn fibonacci(n: i32) -> i32 {
    if n <= 1 {
        return n;
    }

    let a = fibonacci(n - 1);
    let b = fibonacci(n - 2);

    a + b
}
