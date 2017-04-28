
extern {pub fn __VERIFIER_assert(x: i32);
        pub fn __VERIFIER_assume(x: i32);
        pub fn __VERIFIER_nondet_bool() -> bool;
        pub fn __VERIFIER_nondet_signed_char() -> i8;
        pub fn __VERIFIER_nondet_unsigned_char() -> u8;
        pub fn __VERIFIER_nondet_signed_short() -> i16;
        pub fn __VERIFIER_nondet_unsigned_short() -> u16;
        pub fn __VERIFIER_nondet_signed_int() -> i32;
        pub fn __VERIFIER_nondet_unsigned_int() -> u32;
        pub fn __VERIFIER_nondet_signed_long() -> i64;
        pub fn __VERIFIER_nondet_unsigned_long() -> u64;
}

#[macro_export]
macro_rules! assert {
    ( $cond:expr ) => ( unsafe {__VERIFIER_assert($cond as i32);} )
}


#[macro_export]
macro_rules! assert_eq {
    ( $lhs:expr, $rhs:expr ) => ( assert!($lhs == $rhs); )
}

#[macro_export]
macro_rules! assume {
    ( $cond:expr ) => (unsafe { __VERIFIER_assume($cond as i32); })
}

pub fn nondet_u64() -> u64 {
    unsafe{ __VERIFIER_nondet_unsigned_long() }
}
