#[macro_use]
mod smack;
use smack::*;

// @expect error

struct Point(u64, u64);

fn main() {
  let x = Point(1u64.nondet(), 2u64.nondet());
  let y = Point(3u64.nondet(), 4u64.nondet());
  let z = Point(x.0 + y.0, x.1 + y.1);
  let Point(p, q) = z;
  assert!(p < x.0 || q < y.1);
}
