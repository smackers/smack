#[macro_use]
mod smack;
use smack::*;

struct Point<T> {
  pub x: T,
  pub y: T
}

fn main() {
  let a:Point<u8> = Point { x: 7, y: 8 };
  let b:Point<u64> = Point { x: 7, y: 8 };
  assert!(a.x as u64 == b.x);
  assert!(a.y as u64 == b.y);
}