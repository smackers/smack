#[macro_use]
mod smack;
use smack::*;

// @flag --unroll=3 --time-limit=480
// @expect verified

fn main() {
   let mut v1:Vec<u64> = vec![0];
   let mut v2:Vec<u64> = vec![3];
   v1.append(&mut v2);
   assert!(v1[1] == 3);
}
