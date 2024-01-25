fn mutability() {
    let mut sum: i32 = 0;

    for i in 1..100 {
        sum = sum + i;
    }

    let doubled = sum + sum;

    println!("Doubled: {doubled}");

    doubled = 42;
}
