#[macro_use]
extern crate smack;
use smack::*;

// @flag --checked-functions _ZN20targeted_panic_fail212dont_call_me17h.{17}
// @flag --check rust-panics
// @expect error

fn dont_call_me() {
    panic!();
}

fn main() {
    dont_call_me();
}
