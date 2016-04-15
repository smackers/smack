extern {fn __VERIFIER_assert(x: i32);}

macro_rules! assert {
    ( $cond:expr ) => (
        unsafe { __VERIFIER_assert($cond as i32); }
    );
}

fn main() {
    {    
        let x: i32 = 3;
        let y: i32 = 4;
        assert!(x*y == 12);
    }
    {    
        let x: i32 = 3;
        let y: i32 = 4;
        assert!(x*y != 13);
    }
    {    
        let x: u32 = 3;
        let y: u32 = 4;
        assert!(x*y == 12);
    }
    {    
        let x: u32 = 3;
        let y: u32 = 4;
        assert!(x*y != 13);
    }
    {    
        let x: i32 = 3;
        let y: i32 = 4;
        assert!(x+y == 7);
    }
    {    
        let x: i32 = 3;
        let y: i32 = 4;
        assert!(x+y != 8);
    }

    {    
        let x: u32 = 3;
        let y: u32 = 4;
        assert!(x+y == 7);
    }
    {    
        let x: u32 = 3;
        let y: u32 = 4;
        assert!(x+y != 8);
    }


    
}
