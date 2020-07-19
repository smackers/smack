use std::marker::PhantomData;

#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

struct X<T> {
    x: i32,
    phantom: PhantomData<T>, // To consume the generic type: this is zero-sized (type {})
}

struct S<T> {
    pub phantom: X<T>,
    pub data: i32,
}

fn main() {
    let mut x = S::<u64> {
        phantom: X {
            x: 7,
            phantom: PhantomData,
        },
        data: 4,
    };
    x.data += 1;
    smack::assert!(x.data == 5);
}
