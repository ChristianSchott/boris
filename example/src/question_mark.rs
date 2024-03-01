fn may_fail() -> Result<i32, String> {
    todo!()
}

fn question_mark() -> Result<(), String> {
    let x: Result<i32, String> = may_fail();
    let y = x?;
    println!("Success: {}", y);
    Result::Ok(())
}
