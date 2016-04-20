
fn main() {
    {    
        let x: i32 = 3;
        let y: i32 = 4;
        assert_eq!(x*y, 12);
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
    //division
    {    
        let x: u32 = 8;
        let y: u32 = 4;
        assert!(x/y == 2);
    }
    {    
        let x: u32 = 8;
        let y: u32 = 4;
        assert!(x/y != 3);
    }
    {    
        let x: i32 = 8;
        let y: i32 = 4;
        assert!(x/y == 2);
    }
    {    
        let x: i32 = 8;
        let y: i32 = 4;
        assert!(x/y != 3);
    }

    
}
