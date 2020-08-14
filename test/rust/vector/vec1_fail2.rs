#[macro_use]
extern crate smack;
use smack::*;

// @expect error

fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(0);
    v.push(1);
    v.push(3);
    smack::assert!(v[0] == 0);
    smack::assert!(v[1] == 1);
    smack::assert!(v[2] == 3);
    v[2] = v[0] + v[1];
    smack::assert!(v[0] == 0);
    smack::assert!(v[1] != 1);
    smack::assert!(v[2] == 1);
}
