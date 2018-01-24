#[macro_use]
mod smack;
use smack::*;

fn main() {
  let a = 6i32.nondet();
  let b = 7i32.nondet();
  assume!(4 < a && a < 8); // a in [5,7]
  assume!(5 < b && b < 9); // b in [6,8]
  let x = a * b;
  assert!(!(x==30 || x==35 || x==40 || 
            x==36 || x==48 || x==42 || 
            x==49 || x==56)); // a*b != anythin allowed
}
