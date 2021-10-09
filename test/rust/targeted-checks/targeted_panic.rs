#[macro_use]
extern crate smack;
use smack::*;

// @flag --checked-functions main
// @flag --check rust-panics
// @expect verified

#[no_mangle]
fn dont_call_me() {
    panic!();
}

fn main() {
    dont_call_me();
}
