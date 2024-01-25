#[derive(Debug)]
enum EnumDataTest {
    A(i32),
    B(i32),
}

fn ref_into_enum() {
    let mut data = EnumDataTest::A(1);
    let data_ref: &mut i32;
    match &mut data {
        EnumDataTest::A(x) => data_ref = x,
        EnumDataTest::B(x) => data_ref = x,
    }

    *data_ref = 42;
    print!("{:?}", data);
}
