extern {fn __VERIFIER_assert(x: i32);}

macro_rules! assert {
    ( $cond:expr ) => (
        unsafe { __VERIFIER_assert($cond as i32); }
    );
}

fn main() {
    let v = vec![0];
    assert!(0);
    assert!(v[0] == 1);
}
