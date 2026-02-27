/// Wrap "too-large" indexes back into a valid range for the array
fn get_wrapped(i: usize, a: &[u32]) -> u32 {
    if a.len() == 0 {
        return 0;
    }
    return unsafe { *a.as_ptr().add(i % a.len() + 1) };
}

#[cfg(kani)]
#[kani::proof]
fn bound_check() {
    let size: usize = kani::any();
    kani::assume(size < 4096);
    let index: usize = kani::any();
    let array: Vec<u32> = vec![0; size];
    get_wrapped(index, &array);
}

fn get_wrapped_2(i: usize, a: &[u32]) -> u32 {
    return a[i % a.len()];
}

#[cfg(kani)]
#[kani::proof]
fn check_get_wrapped_2() {
    let size: usize = kani::any();
    kani::assume(size < 4096);
    let index: usize = kani::any();
    let array: Vec<u32> = vec![0; size];
    get_wrapped_2(index, &array);
}
