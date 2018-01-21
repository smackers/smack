fn main() {
  let mut a = 1;
  for i in 1..7 as u64 {
    a *= i;
  }
  assert!(a == 720); // a == 6!
}
