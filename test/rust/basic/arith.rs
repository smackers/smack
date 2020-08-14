#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

fn main() {
    // unsigned
    {
        let a: u32 = 2;
        let b: u32 = 3;
        {
            let c = a + b;
            smack::assert!(c == 5);
        }
        {
            let c = a * b;
            smack::assert!(c == 6);
        }
        {
            let c = b - a;
            smack::assert!(c == 1);
        }
        {
            let c = a % b;
            smack::assert!(c == 2);
            let d = b % a;
            smack::assert!(d == 1);
        }
        {
            let c = a / b;
            smack::assert!(c == 0);
            let d = b / a;
            smack::assert!(d == 1);
        }
    }
    // signed
    {
        let a: i32 = -3;
        let b: i32 = 5;
        {
            let c = a + b;
            smack::assert!(c == 2);
        }
        {
            let c = a * b;
            smack::assert!(c == -15);
        }
        {
            let c = b - a;
            smack::assert!(c == 8);
        }
    }
}
