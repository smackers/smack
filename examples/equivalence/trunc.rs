// Modified version from https://github.com/rust-lang/libm/blob/master/src/math/trunc.rs

#[macro_use]
extern crate smack;
use smack::*;

extern crate core;
use core::f64;

pub fn trunc(x: f64) -> f64 {
    let x1p120 = f64::from_bits(0x4770000000000000); // 0x1p120f === 2 ^ 120

    let mut i: u64 = x.to_bits();
    verifier_equiv_assume_u64(i, 0);
    let mut e: i64 = (i >> 52 & 0x7ff) as i64 - 0x3ff + 12;
    let m: u64;

    if e >= 52 + 12 {
        return x;
    }
    if e < 12 {
        e = 1;
    }
    m = -1i64 as u64 >> e;
    verifier_equiv_assume_u64(m, 1);
    verifier_equiv_assume_u64(i & m, 2);

    if (i & m) == 0 {
        return x;
    }
    verifier_equiv_assume_u64(!m, 3);
    verifier_equiv_assume_u64(i & !m, 4);
    i &= !m;
    verifier_equiv_assume_u64(i, 5);
    f64::from_bits(i)
}

extern "C" {
    fn c_trunc(x: f64) -> f64;
    fn __isnan(x: f64) -> i32;
}

fn main() {
    let x = 0.0.verifier_nondet();
    verifier_assume!(__isnan(x) == 0);
    let c_res = unsafe { c_trunc(x) };
    let rust_res = trunc(x);
    verifier_assert!(rust_res == c_res);
}