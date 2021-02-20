#[macro_use]
extern crate smack;
use smack::*;

// @expect error

static mut NUM: i32 = 0;

fn incr(x: i32) -> i32 {
    unsafe {
        NUM += x;
        NUM
    }
}

fn test_print() {
    print!("hola");
    println!("hola");
    print!("hola, senor {}", incr(1));
    println!("hola, senor {}", incr(2));
    print!("hola, senor {0} and senor {1}", 3, incr(3));
    println!("hola, senor {0} and senor {1}", 4, incr(4));
    eprint!("hola");
    eprintln!("hola");
    eprint!("hola, senor {}", incr(1));
    eprintln!("hola, senor {}", incr(2));
    eprint!("hola, senor {0} and senor {1}", 3, incr(3));
    eprintln!("hola, senor {0} and senor {1}", 4, incr(4));
}

fn main() {
    test_print();
    smack::assert!(NUM != 0 + 2 + 4 + 6 + 8);
}
