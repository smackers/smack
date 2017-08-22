//#![feature(alloc)]
//#![feature(heap_api)]
//#![feature(no_std)]
//#![feature(unique)]
//use std::ptr::{Unique, self};
use std::mem;

use label::*;
use verify::SVec;
use std::fmt;

pub type Secret = SVec<u32>;


#[derive(Clone)]
pub struct Labeled<V> {
    pub label: Label,
    val: V
}


extern {
    fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
    fn malloc(size: usize) -> *mut u8;
    fn calloc(count: usize, size: usize) -> *mut u8; 
    fn free(ptr: *mut u8);
    fn __VERIFIER_assert(cond: i32);
//    fn __VERIFIER_assume(cond: i32);
}

fn myrealloc(ptr: *mut u8, old_size: usize, size: usize, align: usize) -> *mut u8 {
    unsafe{realloc(ptr, size)}
}

#[derive(Debug)]
pub struct Arr {
    pub len: usize,
    pub sz: usize,
    pub data: *mut Labeled<Secret>,
}

/*impl fmt::Debug for Arr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Arr {{ len: {}, sz: {}, ptr: {:?} }}",
               self.len, self.sz, *(self.data));
    }
}*/

impl Arr {
    fn new() -> Arr {
        let sz = 20;
        let ds = mem::size_of::<Labeled<Secret>>();
        assert!(ds*sz != 0);
//        println!("Making a vector");
//        let dt = unsafe{(malloc(sz*mem::size_of::<Labeled<Secret>>()))};
        let dt = unsafe{calloc(sz, ds)};
//        assume!(dt as usize != 0);
/*        for i in 0..sz*ds {
            unsafe{ptr::write(dt.offset(i as isize), 0)};
        }*/

        assert!(dt != (0 as *mut u8));
        Arr{len: 0, sz: sz, 
            data: unsafe{mem::transmute::<*mut u8, *mut Labeled<Secret>>(dt)}}
    }
    
    fn get<'a>(&'a self, ind: usize) -> Option<&'a Labeled<Secret>> {
        assert!((self.data as usize) != 0);
        if ind >= self.len {None}
        else{
            let get_result = unsafe{&*(self.data.offset(ind as isize))};
            let label = get_result.label;
//            assert!{label == 5};
            Some(get_result)
        }
    }
    
    fn get_mut<'a>(&'a self, ind: usize) -> Option<&'a mut Labeled<Secret>> {
        if ind >= self.len {return None;}
        Some(unsafe{&mut *(self.data.offset(ind as isize))})
    }
    
    fn set(&mut self, ind: usize, val: Labeled<Secret>) {
        if ind >= self.len {panic!("")}
        unsafe{*(self.data.offset(ind as isize)) = val};
    }
    
    fn push(&mut self, val: Labeled<Secret>) {
//        println!("Pushing vector");
        assert!((self.data as usize) != 0);
        let label = val.label;
        if self.len >= self.sz {
            // Double the length of the array
//            println!("Reallocating");
            self.data = unsafe{myrealloc(self.data as *mut u8, 
                                         mem::size_of::<Labeled<Secret>>()*self.sz, 
                                         mem::size_of::<Labeled<Secret>>()*2*self.sz, 4)} as *mut Labeled<Secret>;
//            if self.data as usize == 0 {panic!{"Failed to reallocate"}};
            self.sz *= 2;
        }
        unsafe{*(self.data.offset(self.len as isize)) = val};
        assert!((self.data as usize) != 0);
        let label2 = unsafe{(*(self.data.offset(self.len as isize))).label};
        assert!(label == label2);
        self.len += 1;
    }
    fn append(&mut self, other: &mut Arr) {
        for i in 0..other.len {
            self.push((*(other.get(i).unwrap())).clone());
        }
    }
}

impl Drop for Arr {
    fn drop(&mut self) {
        // Check null pointer
        //        assert!((self.data as isize) != 0);
//        println!("Dropping");
        if (self.data as isize) == 0 {
            panic!("Null pointer while dropping array!");
        }
        unsafe{free(self.data as *mut u8)};
        self.data = 0 as *mut Labeled<Secret>;
    }
}
// End MB addition
// End arr

#[macro_export]
macro_rules! arr {
    ( $( $x:expr ),* ) => {
            {
                let mut temp_vec = Arr::new();
                assert!(temp_vec.data as usize != 0);
                $(
                    temp_vec.push($x);
                )*
                    temp_vec
            }
    };
} 


#[derive(Debug)]
pub struct SecVec {
    pub m: Arr
}

impl SecVec {
    pub fn new() -> SecVec {
        SecVec {
            m: Arr::new()
        }
    }
    pub fn push(&mut self, v: Secret, l:Label) {
	self.m.push(Labeled{label:l, val:v})
    }

    pub fn update(&mut self, k: usize, mut v: Secret /*l*/, l:Label) {
        match self.m.get_mut(k) {
            Some(old) => {
		old.val.append(&mut v);
		old.label = combine_labels(l, old.label);
            },
            None    => {}
        }
    }

    pub fn get(&self, k:usize, l:Label) -> Option<&Secret>/*l*/ {
        let result = 
            match self.m.get(k) {
                Some(v) => if v.label > l {
                    None
                } else {
                    Some(&v.val)/*l*/
                },
                None    => None
            };
        result
    }

//    pub fn take(&mut self, k:u32, l:Label) -> Option<Secret>/*l*/ {
//        match self.m.remove(&k) {
//            Some(v) => {
//                let Labeled{label, val} = v;
//                if label > l {
//                    None
//                } else {
//                    Some(val)/*l*/
//                }
//            },
//            None    => None
//        }
//    }
}

/*
#[derive(Debug)]
enum Document<V> {
    Unclassified(V),
    Classified(V)
}


use self::Document::*;

pub struct StaticSecHashMap {
    m: HashMap<u32,Document<Secret>>
}

impl StaticSecHashMap {
    pub fn new() -> StaticSecHashMap {
        StaticSecHashMap {
            m: HashMap::new()
        }
    }

    pub fn update_u(&mut self, k: u32, mut v: Secret) {
        match self.m.remove(&k) {
            Some(Classified(mut val)) => {
                val.append(&mut v);
                self.m.insert(k, Classified(val));
            },
            Some(Unclassified(mut val)) => {
                val.append(&mut v);
                self.m.insert(k, Unclassified(val));
            },
            None => {self.m.insert(k, Unclassified(v));}
        }
    }

    pub fn update_c(&mut self, k: u32, mut v: Secret) {
        match self.m.remove(&k) {
            Some(Classified(mut val)) => {
                val.append(&mut v);
                self.m.insert(k, Classified(val));
            },
            Some(Unclassified(mut val)) => {
                val.append(&mut v);
                self.m.insert(k, Classified(val));
            },
            None    => {self.m.insert(k, Classified(v));}
        }
    }

    pub fn get_u(&self, k:u32) -> Option<&Secret> {
        match self.m.get(&k) {
            Some(&Unclassified(ref v)) => Some(&v),
            _                          => None
        }
    }

    pub fn get_c(&self, k:u32) -> Option<&Secret> {
        match self.m.get(&k) {
            Some(&Unclassified(ref v)) => Some(&v),
            Some(&Classified(ref v))   => Some(&v),
            _                          => None
        }
    }
}*/
