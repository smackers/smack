#[macro_use]
extern crate smack;
use smack::*;

// @flag --checked-functions dont_call_me
// @flag --check rust-panics
// @expect error

#[no_mangle]
fn dont_call_me() {
    panic!();
}

fn main() {
    dont_call_me();
}
