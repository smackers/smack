#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn call_with_one<F>(mut some_closure: F) -> ()
where
    F: FnMut(i32) -> (),
{
    some_closure(1);
}

fn main() {
    let mut num = 5i32.verifier_nondet();
    let old_num = num;
    {
        let mut add_num = |x: i32| num += x;

        add_num(5);
        call_with_one(&mut add_num);
    }
    smack::assert!(old_num + 6 != num); // Should be old_num + 6
}
