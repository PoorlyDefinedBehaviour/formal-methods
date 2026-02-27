fn simple_addition(a: u32, b: u32) -> u32 {
    return a + b;
}

#[cfg(kani)]
#[kani::proof]
fn check_simple_addition() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    simple_addition(a, b);
}
