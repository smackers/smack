#[macro_use]
extern crate smack;
use smack::*;

// @expect error

struct Point(u64, u64);

fn main() {
    let x = Point(1u64.verifier_nondet(), 2u64.verifier_nondet());
    let y = Point(3u64.verifier_nondet(), 4u64.verifier_nondet());
    let z = Point(x.0 + y.0, x.1 + y.1);
    let Point(p, q) = z;
    smack::assert!(p < x.0 || q < y.1);
}
