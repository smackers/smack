#[macro_use]
mod smack;
use smack::*;

use std::ops::{Add, AddAssign};

#[derive(PartialEq,Clone,Copy)]
struct Point {
  x: u64,
  y: u64
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
  let a = Point::new(1,2);
  let b = Point::new(3,4);
  let c = a + b;
  assert!(c == Point::new(4,6));
}
