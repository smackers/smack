#![no_std]
#![feature(lang_items)]
#![feature(start)]
use core::panic::PanicInfo;

// @flag --check=rust-panics
// @expect error
// @checkout grep "SMACK found an error: Rust panic."

#[start]
fn main(_x: isize, _y: *const *const u8) -> isize {
    panic!("Something {}", 7);
}

#[panic_handler]
fn panic(_expr: &PanicInfo) -> ! {
    loop {}
}

#[lang = "eh_personality"]
fn eh() {

}
