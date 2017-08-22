fn fib(n: i32) -> Option<u32> {
    if n < 0 { None }
    else {
        let mut x = n;
        let mut a = 0;
        let mut b = 1;
        while x > 0 {
            let b_t = a + b;
            a = b_t;
            b = a;
            x -= 1;
        }
        Some(a)
    }
}

fn main() {
    match fib(5) {
        None => assert!(false),
        Some(v) =>
            assert!(v == 16)
    };
}
