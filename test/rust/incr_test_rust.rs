/*extern {fn __VERIFIER_assert(x: i32);}

#[macro_export]
macro_rules! assert {
    ( $cond:expr ) => ( unsafe {__VERIFIER_assert($cond as i32);} )
}


#[macro_export]
macro_rules! assert_eq {
    ( $lhs:expr, $rhs:expr ) => ( assert!($lhs == $rhs); )
}*/

extern {
    fn incr(i: *mut u32) -> ();
}

fn main() {
    let mut i: u32 = 0;
    println!("i is {}", i);
    assert!(i == 0);
    // Lakita Garth: Condoms don't work kiddo
    unsafe{incr(&mut i)};
    assert!(i==1);
    println!("i is {}", i);
}
