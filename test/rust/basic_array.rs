


//test



#![feature(alloc)]
extern crate alloc;
use alloc::heap::allocate;

struct Arr {
    sz: usize,
    data: *mut i32,
}

impl Arr {
    fn new(sz: usize) -> Arr {
        let dt = unsafe{allocate(sz*4,4)};
        for i in 0..sz {
            unsafe{(*(dt.offset(i as isize))) = 0};
        }
        Arr{sz: sz, data: dt as *mut i32}
    }

    fn get(&self, ind: usize) -> i32 {
        if ind >= self.sz {panic!("")}
        unsafe{*(self.data.offset(ind as isize))}
    }

    fn set(&mut self, ind: usize, val: i32) {
        if ind >= self.sz {panic!("")}
        unsafe{*(self.data.offset(ind as isize)) = val};
    }
}

fn main() {
    let sz = 5;
    let mut arr = Arr::new(sz);
    for ind in 0..sz {
        arr.set(ind as usize, ind as i32);
    }
    for ind in 0..sz {
        println!("{}", arr.get(ind));
    }
    
    // The array seems to work!!!
    for ind in 0..sz {
        assert!(arr.get(ind) == ind as i32);
    }

    for ind in 0..sz {
        assert!(arr.get(ind) != (ind + 1) as i32);
    }

    // Mutate the array

    for ind in 0..sz {
        arr.set((sz-ind-1) as usize, (sz-ind-1) as i32);
    }
    
    // Check again...

    for ind in 0..sz {
        assert!(arr.get(sz-ind-1) == (sz-ind-1) as i32);
    }

    for ind in 0..sz {
        assert!(arr.get(sz-ind-1) != ((sz-ind)+3) as i32);
    }


}
