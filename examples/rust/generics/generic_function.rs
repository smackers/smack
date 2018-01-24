#[macro_use]
mod smack;
use smack::*;

struct Point {
  pub x:u64,
  pub y:u64
}

trait D {
  fn double(self) -> Self;
}

impl D for u8 {
  fn double(self) -> Self {
    2*self
  }
}

impl D for Point {
  fn double(self) -> Self {
    Point { x: 2*self.x, y: 2*self.y }
  }
}

fn double<T: D>(x: T) -> T {
  x.double()
}

fn main() {
  let a:u8 = 17;
  let p = Point { x: 3, y: 4 };
  let b = double(a);
  let q = double(p);
  assert!(b == 34);
  assert!(q.x == 6);
  assert!(q.y == 8);
}
