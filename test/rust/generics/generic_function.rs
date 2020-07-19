#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

struct Point<T> {
    pub x: T,
    pub y: T,
}

struct Point3<T> {
    pub x: T,
    pub y: T,
    pub z: T,
}

trait S<T> {
    fn swap_items(self) -> Self;
}

impl<T> S<T> for Point<T> {
    fn swap_items(self) -> Point<T> {
        Point::<T> {
            x: self.y,
            y: self.x,
        }
    }
}

impl<T> S<T> for Point3<T> {
    fn swap_items(self) -> Point3<T> {
        Point3::<T> {
            x: self.y,
            y: self.z,
            z: self.x,
        }
    }
}

fn swapem<T, U: S<T>>(s: U) -> U {
    s.swap_items()
}

fn main() {
    let x2 = 7i64.verifier_nondet();
    let y2 = 8i64.verifier_nondet();
    let x3 = 1i64.verifier_nondet();
    let y3 = 2i64.verifier_nondet();
    let z3 = 3i64.verifier_nondet();
    let p2 = Point::<i64> { x: x2, y: y2 };
    let p3 = Point3::<i64> {
        x: x3,
        y: y3,
        z: z3,
    };

    let q2 = swapem(p2);
    let q3 = swapem(p3);
    smack::assert!(q2.x == y2);
    smack::assert!(q2.y == x2);
    smack::assert!(q3.x == y3);
    smack::assert!(q3.y == z3);
    smack::assert!(q3.z == x3);
}
