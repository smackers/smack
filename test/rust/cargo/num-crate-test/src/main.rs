extern crate num_traits;
#[macro_use]
extern crate smack;
use smack::*;

fn main() {
    let a: u32 = 5.verifier_nondet();
    let b: u32 = 3.verifier_nondet();
    let c: u32 = 8.verifier_nondet();
    verifier_assume!(a <= c);
    let d = num_traits::clamp(b, a, c);
    verifier_assert!(a <= d && d <= c);
}
