#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

struct Point {
    x: i32,
    y: i32,
}

struct Pair {
    x: Point,
    y: Point,
}

fn valid(p: &Pair) -> bool {
    p.x.x != p.y.x || p.x.y != p.y.y
}

fn main() {
    let x = Point {
        x: 1i32.verifier_nondet(),
        y: 2i32.verifier_nondet(),
    };
    let y = Point {
        x: 2i32.verifier_nondet(),
        y: 3i32.verifier_nondet(),
    };
    smack::assume!(x.x != y.x);
    let p = Pair { x: x, y: y };
    smack::assert!(valid(&p));
}
