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
    fn init();
    fn get_x() -> *mut i32;
    fn get_elem(i: usize) -> *mut i32;
    fn set_elem(i: usize, a: i32);
    fn finalize();
}

fn main() {
    unsafe{init()};
    let x = unsafe {get_elem(101)};
    let y = unsafe{*x};
    println!("{}", y);
    unsafe{finalize()};
}
