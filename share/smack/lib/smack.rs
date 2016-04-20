extern {fn __VERIFIER_assert(x: i32);}

#[macro_export]
macro_rules! assert {
    ( $cond:expr ) => ( unsafe {__VERIFIER_assert($cond as i32);} )
}


#[macro_export]
macro_rules! assert_eq {
    ( $lhs:expr, $rhs:expr ) => ( assert!($lhs == $rhs); )
}


