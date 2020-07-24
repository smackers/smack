// @flag --check=rust-panics
// @expect error
// @checkout grep "SMACK found an error: Rust panic."

fn main() {
    panic!("{}", 7);
}
