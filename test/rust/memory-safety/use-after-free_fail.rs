use std::ptr;

// Simplified from Qin et al. fig. 7

unsafe fn run(data: *const u8) -> bool {
    if data.is_null() { false }
    else { *data == 0 }
}

fn sign(data: Option<&[u8]>) -> bool {
    let p = match data {
	Some(d) => Box::new(d).as_ptr(),
	None => ptr::null_mut(),
    }; // Lifetime of temporary Box ends
    unsafe {
	run(p)
    }
}


fn main() {
    let data = [0u8; 2];
    sign(Some(&data));
}
