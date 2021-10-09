// @flag --check=memory-safety --unroll=2
// @expect errro


fn sum_to(slice: &[u8], to: usize) -> u64 {
    // This function bypasses rust bounds checking. to must be less than or
    // equal to the length of the slice.
    
    // if slice.len() < to { panic!(); }
    let slice_ptr = slice.as_ptr();
    let mut sum = 0;
    // Bypass bounds checking
    unsafe {
	for idx in 0..to {
	    sum += *slice_ptr.add(idx) as u64;
	}
    }
    sum
}


fn main() {
    let x = [1];
    sum_to(&x, 2);
}
