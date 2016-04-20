extern {fn __VERIFIER_assert(x: i32);}

macro_rules! assert {
    ( $cond:expr ) => (
        unsafe { __VERIFIER_assert($cond as i32); }
    );
}

fn main() {
    // Shift right
    {
        let x: i32 = 3;
        let y = x >> 1;
        assert!(y == 1);
    }
    {
        let x: i32 = 3;
        let y = x >> 1;
        assert!(y != 2);
    }
    {
        let x: i64 = 3;
        let y = x >> 1;
        assert!(y == 1);
    }
    {
        let x: i64 = 3;
        let y = x >> 1;
        assert!(y != 2);
    }
    {
        let x: i16 = 3;
        let y = x >> 1;
        assert!(y == 1);
    }
    {
        let x: i16 = 3;
        let y = x >> 1;
        assert!(y != 2);
    }
    {
        let x: i8 = 3;
        let y = x >> 1;
        assert!(y == 1);
    }
    {
        let x: i8 = 3;
        let y = x >> 1;
        assert!(y != 2);
    }

    // Shift left
    {
        let x: i32 = 3;
        let y = x << 1;
        assert!(y == 6);
    }
    {
        let x: i32 = 3;
        let y = x << 1;
        assert!(y != 2);
    }
    {
        let x: i64 = 3;
        let y = x << 1;
        assert!(y == 6);
    }
    {
        let x: i64 = 3;
        let y = x << 1;
        assert!(y != 2);
    }
    {
        let x: i16 = 3;
        let y = x << 1;
        assert!(y == 6);
    }
    {
        let x: i16 = 3;
        let y = x << 1;
        assert!(y != 2);
    }
    {
        let x: i8 = 3;
        let y = x << 1;
        assert!(y == 6);
    }
    {
        let x: i8 = 3;
        let y = x << 1;
        assert!(y != 2);
    }
}
