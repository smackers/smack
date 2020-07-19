#[macro_use]
extern crate smack;
use smack::*;

// @expect error

use std::ops::{Add, AddAssign};

#[derive(PartialEq, Clone, Copy)]
struct Point {
    x: u64,
    y: u64,
}

impl Point {
    pub fn new(_x: u64, _y: u64) -> Point {
        Point { x: _x, y: _y }
    }
    pub fn get_x(self) -> u64 {
        self.x
    }
    pub fn get_y(self) -> u64 {
        self.y
    }
}

impl Add for Point {
    type Output = Point;
    fn add(self, other: Point) -> Point {
        Point::new(self.x + other.x, self.y + other.y)
    }
}

impl AddAssign for Point {
    fn add_assign(&mut self, other: Point) {
        self.x += other.x;
        self.y += other.y;
    }
}

fn main() {
    let w = 1u64.verifier_nondet();
    let x = 2u64.verifier_nondet();
    let y = 3u64.verifier_nondet();
    let z = 4u64.verifier_nondet();

    let a = Point::new(w, x);
    let b = Point::new(y, z);
    let c = a + b;
    smack::assert!(c != Point::new(w + y, x + z));
}
