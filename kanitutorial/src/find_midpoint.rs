fn find_midpoint(low: u32, high: u32) -> u32 {
    return (low + high) / 2;
}

#[cfg(kani)]
#[kani::proof]
fn check_find_midpoint() {
    let low: u32 = kani::any();
    let high: u32 = kani::any();
    find_midpoint(low, high);
}
