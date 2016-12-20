fn main() {
    //multiplication
    {    
        let x: i64 = 3;
        let y: i64 = 4;
        assert!(x*y == 12);
    }
    {    
        let x: i64 = 3;
        let y: i64 = 4;
        assert!(x*y != 13);
    }
    {    
        let x: u64 = 3;
        let y: u64 = 4;
        assert!(x*y == 12);
    }
    {    
        let x: u64 = 3;
        let y: u64 = 4;
        assert!(x*y != 13);
    }
    //addition
    {    
        let x: i64 = 3;
        let y: i64 = 4;
        assert!(x+y == 7);
    }
    {    
        let x: i64 = 3;
        let y: i64 = 4;
        assert!(x+y != 8);
    }
    {    
        let x: u64 = 3;
        let y: u64 = 4;
        assert!(x+y == 7);
    }
    {    
        let x: u64 = 3;
        let y: u64 = 4;
        assert!(x+y != 8);
    }
    //division
    {    
        let x: u64 = 8;
        let y: u64 = 4;
        assert!(x/y == 2);
    }
    {    
        let x: u64 = 8;
        let y: u64 = 4;
        assert!(x/y != 3);
    }
    {    
        let x: i64 = 8;
        let y: i64 = 4;
        assert!(x/y == 2);
    }
    {    
        let x: i64 = 8;
        let y: i64 = 4;
        assert!(x/y != 3);
    }
}