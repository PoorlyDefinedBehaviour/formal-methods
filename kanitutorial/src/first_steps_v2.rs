fn estimate_size(x: u32) -> u32 {
    assert!(x < 4096);

    if x < 256 {
        if x < 128 {
            return 1;
        } else {
            return 3;
        }
    } else if x < 1024 {
        if x > 1022 {
            return 4;
        } else {
            return 5;
        }
    } else {
        if x < 2048 {
            return 7;
        } else {
            return 9;
        }
    }
}

#[cfg(kani)]
#[kani::proof]
fn check_estimate_size() {
    let x: u32 = kani::any();
    kani::assume(x < 4096);
    let y = estimate_size(x);
    assert!(y < 10);
}
