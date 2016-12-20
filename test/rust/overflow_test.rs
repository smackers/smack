fn main() {
    let mut i: u32 = 0;
    let mut x: u32 = 1;
    while i < 32 {
        x *= 2;
        i += 1;
    }
    println!("{}", x);
}
