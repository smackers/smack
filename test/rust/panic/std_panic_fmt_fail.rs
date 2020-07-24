// @flag --check=rust-panics
// @expect error

fn main() {
    panic!("{}", 7);
}
