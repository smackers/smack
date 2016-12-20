
//test

#![feature(alloc)]


extern {
    fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
}

fn myrealloc(ptr: *mut u8, old_size: usize, size: usize, align: usize) -> *mut u8 {
    unsafe{realloc(ptr, size)}
}


extern crate alloc;
use alloc::heap::{allocate,deallocate,reallocate};

struct Arr {
    len: usize,
    sz: usize,
    data: *mut i32,
}

impl Arr {
    fn new(sz: usize) -> Arr {
        if sz == 0 {panic!("")};
        let dt = unsafe{allocate(sz*4,4)};
        for i in 0..sz {
            unsafe{(*(dt.offset(i as isize))) = 0};
        }
        Arr{len: 0, sz: sz, data: dt as *mut i32}
    }

    fn get(&self, ind: usize) -> i32 {
        if ind >= self.len {panic!("{} {}", ind, self.len)}
        unsafe{*(self.data.offset(ind as isize))}
    }

    fn set(&mut self, ind: usize, val: i32) {
        if ind >= self.len {panic!("")}
        unsafe{*(self.data.offset(ind as isize)) = val};
    }

    fn push(&mut self, val: i32) {
        if self.len >= self.sz {
            // Double the length of the array
            println!("Reallocating");
            self.data = unsafe{myrealloc(self.data as *mut u8, 4*self.sz, 4*2*self.sz, 4)} as *mut i32;
            if self.data as usize == 0 {panic!{"Failed to reallocate"}};
            self.sz *= 2;
        }
        unsafe{*(self.data.offset(self.len as isize)) = val};
        self.len += 1;
    }
}

impl Drop for Arr {
    fn drop(&mut self) {
        // Check null pointer
        //        assert!((self.data as isize) != 0);
        println!("Dropping");
        if (self.data as isize) == 0 {
            panic!("Null pointer while dropping array!");
        }
        unsafe{deallocate((self.data as *mut u8), self.sz*4, 4)};
        self.data = 0 as *mut i32;
    }
}

fn main() {
    let mut len = 2;
    let mut arr = Arr::new(len);
    let mut ind = 0;

    while ind < len {
        arr.push(ind as i32);
        ind += 1;
    }

    ind = 0;
    while ind < len {
        println!("{}", arr.len);
        assert!(arr.len == 2);
        assert!(arr.get(ind) == ind as i32);
        println!("{}", arr.get(ind));
        ind += 1;
    }

    // Test reallocation
    ind = 0;
    while ind < len {
        println!("{}", arr.len);
        arr.push((ind + 2) as i32);
        ind += 1;
    }
    println!("{}", arr.len);
    assert!(arr.len == 4);
    len *= 2;
    assert!(len == 4);
    ind = 0;
    assert!(arr.get(0) == 0);
    while ind < len {
        println!("{}", arr.get(ind));
        assert!(arr.get(ind) == ind as i32);
        ind += 1
    }

    // The array seems to work!!!
    for ind in 0..len {
        assert!(arr.get(ind) == ind as i32);
    }

    for ind in 0..len {
        assert!(arr.get(ind) != (ind + 1) as i32);
    }

    // Mutate the array

    for ind in 0..len {
        arr.set((len-ind-1) as usize, (len-ind-1) as i32);
    }
    
    // Check again...

    for ind in 0..len {
        assert!(arr.get(len-ind-1) == (len-ind-1) as i32);
    }

    for ind in 0..len {
        assert!(arr.get(len-ind-1) != ((len-ind)+3) as i32);
    }


}
