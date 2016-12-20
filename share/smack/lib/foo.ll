;; i8
define { i8, i1 } @smack.llvm.smul.with.overflow.i8(i8 %bar.coerce0, i8 %bar.coerce1) #0 {
entry:
  %0 = alloca { i8, i1 }
  %1 = getelementptr { i8, i1 }, { i8, i1 }* %0, i8 0, i8 0
  %2 = mul i8 %bar.coerce0, %bar.coerce1 
  store i8 %2, i8* %1
  %c1 = icmp sle i8 %2, i8 127
  call void @__VERIFIER_assert(i8 %c1)
  %c2 = icmp sgt i8 %2, i8 -128
  call void @__VERIFIER_assert(i8 %c2)
  %3 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 1
  store i1 0, i1* %3
  %4 = load { i8, i1 }, {i8, i1}* %0
  ret { i8, i1 } %4
}

define { i8, i1 } @smack.llvm.umul.with.overflow.i8(i8 %bar.coerce0, i8 %bar.coerce1) #0 {
entry:
  %0 = alloca { i8, i1 }
  %1 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 0
  %2 = mul i8 %bar.coerce0, %bar.coerce1 
  store i8 %2, i8* %1
  %c1 = icmp ule i8 %2, i8 255
  call void @__VERIFIER_assert(i8 %c1)
  %c2 = icmp ugt i8 %2, i8 0
  call void @__VERIFIER_assert(i8 %c2)
  %3 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 1
  store i1 0, i1* %3
  %4 = load { i8, i1 }, {i8, i1}* %0
  ret { i8, i1 } %4
}

define { i8, i1 } @smack.llvm.sadd.with.overflow.i8(i8 %bar.coerce0, i8 %bar.coerce1) #0 {
entry:
  %0 = alloca { i8, i1 }
  %1 = getelementptr { i8, i1 }, { i8, i1 }* %0, i8 0, i8 0
  %2 = add i8 %bar.coerce0, %bar.coerce1 
  store i8 %2, i8* %1
  %c1 = icmp sle i8 %2, i8 127
  call void @__VERIFIER_assert(i8 %c1)
  %c2 = icmp sgt i8 %2, i8 -128
  call void @__VERIFIER_assert(i8 %c2)
  %3 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 1
  store i1 0, i1* %3
  %4 = load { i8, i1 }, {i8, i1}* %0
  ret { i8, i1 } %4
}

define { i8, i1 } @smack.llvm.usub.with.overflow.i8(i8 %bar.coerce0, i8 %bar.coerce1) #0 {
entry:
  %0 = alloca { i8, i1 }
  %1 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 0
  %2 = sub i8 %bar.coerce0, %bar.coerce1 
  store i8 %2, i8* %1
  %c1 = icmp ule i8 %2, i8 255
  call void @__VERIFIER_assert(i8 %c1)
  %c2 = icmp ugt i8 %2, i8 0
  call void @__VERIFIER_assert(i8 %c2)
  %3 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 1
  store i1 0, i1* %3
  %4 = load { i8, i1 }, {i8, i1}* %0
  ret { i8, i1 } %4
}

define { i8, i1 } @smack.llvm.ssub.with.overflow.i8(i8 %bar.coerce0, i8 %bar.coerce1) #0 {
entry:
  %0 = alloca { i8, i1 }
  %1 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 0
  %2 = sub i8 %bar.coerce0, %bar.coerce1 
  store i8 %2, i8* %1
  %c1 = icmp sle i8 %2, i8 127
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i8 %2, i8 -128
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 1
  store i1 0, i1* %3
  %4 = load { i8, i1 }, {i8, i1}* %0
  ret { i8, i1 } %4
}

define { i8, i1 } @smack.llvm.udiv.with.overflow.i8(i8 %bar.coerce0, i8 %bar.coerce1) #0 {
entry:
  %0 = alloca { i8, i1 }
  %1 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 0
  %2 = sdiv i8 %bar.coerce0, %bar.coerce1 
  store i8 %2, i8* %1
  %c1 = icmp ule i8 %2, i8 255
  call void @__VERIFIER_assert(i8 %c1)
  %c2 = icmp ugt i8 %2, i8 0
  call void @__VERIFIER_assert(i8 %c2)
  %3 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 1
  store i1 0, i1* %3
  %4 = load { i8, i1 }, {i8, i1}* %0
  ret { i8, i1 } %4
}

define { i8, i1 } @smack.llvm.sdiv.with.overflow.i8(i8 %bar.coerce0, i8 %bar.coerce1) #0 {
entry:
  %0 = alloca { i8, i1 }
  %1 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 0
  %2 = sdiv i8 %bar.coerce0, %bar.coerce1 
  store i8 %2, i8* %1
  %c1 = icmp sle i8 %2, i8 127
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i8 %2, i8 -128
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 1
  store i1 0, i1* %3
  %4 = load { i8, i1 }, {i8, i1}* %0
  ret { i8, i1 } %4
}

define { i8, i1 } @smack.llvm.uadd.with.overflow.i8(i8 %bar.coerce0, i8 %bar.coerce1) #0 {
entry:
  %0 = alloca { i8, i1 }
  %1 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 0
  %2 = add i8 %bar.coerce0, %bar.coerce1 
  store i8 %2, i8* %1
  %c1 = icmp ule i8 %2, i8 255
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i8 %2, i8 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i8, i1 }, {i8, i1}* %0, i8 0, i8 1
  store i1 0, i1* %3
  %4 = load { i8, i1 }, {i8, i1}* %0
  ret { i8, i1 } %4
}

;; i16
define { i16, i1 } @smack.llvm.smul.with.overflow.i16(i16 %bar.coerce0, i16 %bar.coerce1) #0 {
entry:
  %0 = alloca { i16, i1 }
  %1 = getelementptr { i16, i1 }, { i16, i1 }* %0, i16 0, i16 0
  %2 = mul i16 %bar.coerce0, %bar.coerce1 
  store i16 %2, i16* %1
  %c1 = icmp sle i16 %2, i16 32767
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i16 %2, i16 -32768
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 1
  store i1 0, i1* %3
  %4 = load { i16, i1 }, {i16, i1}* %0
  ret { i16, i1 } %4
}

define { i16, i1 } @smack.llvm.umul.with.overflow.i16(i16 %bar.coerce0, i16 %bar.coerce1) #0 {
entry:
  %0 = alloca { i16, i1 }
  %1 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 0
  %2 = mul i16 %bar.coerce0, %bar.coerce1 
  store i16 %2, i16* %1
  %c1 = icmp ule i16 %2, i16 65535
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i16 %2, i16 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 1
  store i1 0, i1* %3
  %4 = load { i16, i1 }, {i16, i1}* %0
  ret { i16, i1 } %4
}

define { i16, i1 } @smack.llvm.ssub.with.overflow.i16(i16 %bar.coerce0, i16 %bar.coerce1) #0 {
entry:
  %0 = alloca { i16, i1 }
  %1 = getelementptr { i16, i1 }, { i16, i1 }* %0, i16 0, i16 0
  %2 = sub i16 %bar.coerce0, %bar.coerce1 
  store i16 %2, i16* %1
  %c1 = icmp sle i16 %2, i16 32767
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i16 %2, i16 -32768
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 1
  store i1 0, i1* %3
  %4 = load { i16, i1 }, {i16, i1}* %0
  ret { i16, i1 } %4
}

define { i16, i1 } @smack.llvm.usub.with.overflow.i16(i16 %bar.coerce0, i16 %bar.coerce1) #0 {
entry:
  %0 = alloca { i16, i1 }
  %1 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 0
  %2 = sub i16 %bar.coerce0, %bar.coerce1 
  store i16 %2, i16* %1
  %c1 = icmp ule i16 %2, i16 65535
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i16 %2, i16 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 1
  store i1 0, i1* %3
  %4 = load { i16, i1 }, {i16, i1}* %0
  ret { i16, i1 } %4
}

define { i16, i1 } @smack.llvm.sdiv.with.overflow.i16(i16 %bar.coerce0, i16 %bar.coerce1) #0 {
entry:
  %0 = alloca { i16, i1 }
  %1 = getelementptr { i16, i1 }, { i16, i1 }* %0, i16 0, i16 0
  %2 = sdiv i16 %bar.coerce0, %bar.coerce1 
  store i16 %2, i16* %1
  %c1 = icmp sle i16 %2, i16 32767
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i16 %2, i16 -32768
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 1
  store i1 0, i1* %3
  %4 = load { i16, i1 }, {i16, i1}* %0
  ret { i16, i1 } %4
}

define { i16, i1 } @smack.llvm.udiv.with.overflow.i16(i16 %bar.coerce0, i16 %bar.coerce1) #0 {
entry:
  %0 = alloca { i16, i1 }
  %1 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 0
  %2 = udiv i16 %bar.coerce0, %bar.coerce1 
  store i16 %2, i16* %1
  %c1 = icmp ule i16 %2, i16 65535
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i16 %2, i16 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 1
  store i1 0, i1* %3
  %4 = load { i16, i1 }, {i16, i1}* %0
  ret { i16, i1 } %4
}

define { i16, i1 } @smack.llvm.sadd.with.overflow.i16(i16 %bar.coerce0, i16 %bar.coerce1) #0 {
entry:
  %0 = alloca { i16, i1 }
  %1 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 0
  %2 = add i16 %bar.coerce0, %bar.coerce1 
  store i16 %2, i16* %1
  %c1 = icmp sle i16 %2, i16 32767
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i16 %2, i16 -32768
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 1
  store i1 0, i1* %3
  %4 = load { i16, i1 }, {i16, i1}* %0
  ret { i16, i1 } %4
}

define { i16, i1 } @smack.llvm.uadd.with.overflow.i16(i16 %bar.coerce0, i16 %bar.coerce1) #0 {
entry:
  %0 = alloca { i16, i1 }
  %1 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 0
  %2 = add i16 %bar.coerce0, %bar.coerce1 
  store i16 %2, i16* %1
  %c1 = icmp ule i16 %2, i16 65535
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i16 %2, i16 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i16, i1 }, {i16, i1}* %0, i16 0, i16 1
  store i1 0, i1* %3
  %4 = load { i16, i1 }, {i16, i1}* %0
  ret { i16, i1 } %4
}

;; i32
define { i32, i1 } @smack.llvm.smul.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }, { i32, i1 }* %0, i32 0, i32 0
  %2 = mul i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %c1 = icmp sle i32 %2, i32 2147483647
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i32 %2, i32 -2147483648
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }, {i32, i1}* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smack.llvm.umul.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 0
  %2 = mul i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %c1 = icmp ule i32 %2, i32 4294967295
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i32 %2, i32 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }, {i32, i1}* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smack.llvm.ssub.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }, { i32, i1 }* %0, i32 0, i32 0
  %2 = sub i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %c1 = icmp sle i32 %2, i32 2147483647
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i32 %2, i32 -2147483648
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }, {i32, i1}* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smack.llvm.usub.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 0
  %2 = sub i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %c1 = icmp ule i32 %2, i32 4294967295
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i32 %2, i32 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }, {i32, i1}* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smack.llvm.sdiv.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }, { i32, i1 }* %0, i32 0, i32 0
  %2 = sdiv i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %c1 = icmp sle i32 %2, i32 2147483647
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i32 %2, i32 -2147483648
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }, {i32, i1}* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smack.llvm.udiv.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 0
  %2 = udiv i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %c1 = icmp ule i32 %2, i32 4294967295
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i32 %2, i32 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }, {i32, i1}* %0
  ret { i32, i1 } %4
}


define { i32, i1 } @smack.llvm.sadd.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 0
  %2 = add i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %c1 = icmp sle i32 %2, i32 2147483647
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i32 %2, i32 -2147483648
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }, {i32, i1}* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smack.llvm.uadd.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 0
  %2 = add i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %c1 = icmp ule i32 %2, i32 4294967295
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i32 %2, i32 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i32, i1 }, {i32, i1}* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }, {i32, i1}* %0
  ret { i32, i1 } %4
}

;; i64
define { i64, i1 } @smack.llvm.smul.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 0
  %2 = mul i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %c1 = icmp sle i64 %2, i64  9223372036854775807
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i64 %2, i64 -9223372036854775808
  call void @__VERIFIER_assert(i64 %c2)
  %3 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1}, { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smack.llvm.umul.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 0
  %2 = mul i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %c1 = icmp ule i64 %2, i64  18446744073709551615
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i64 %2, i64 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1}, { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smack.llvm.ssub.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 0
  %2 = sub i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %c1 = icmp sle i64 %2, i64  9223372036854775807
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i64 %2, i64 -9223372036854775808
  call void @__VERIFIER_assert(i64 %c2)
  %3 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1}, { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smack.llvm.usub.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 0
  %2 = sub i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %c1 = icmp ule i64 %2, i64  18446744073709551615
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i64 %2, i64 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1}, { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smack.llvm.sdiv.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 0
  %2 = sdiv i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %c1 = icmp sle i64 %2, i64  9223372036854775807
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i64 %2, i64 -9223372036854775808
  call void @__VERIFIER_assert(i64 %c2)
  %3 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1}, { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smack.llvm.udiv.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 0
  %2 = udiv i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %c1 = icmp ule i64 %2, i64  18446744073709551615
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i64 %2, i64 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1}, { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smack.llvm.sadd.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 0
  %2 = add i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %c1 = icmp sle i64 %2, i64  9223372036854775807
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp sgt i64 %2, i64 -9223372036854775808
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1}, { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smack.llvm.uadd.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 0
  %2 = add i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %c1 = icmp ule i64 %2, i64  18446744073709551615
  call void @__VERIFIER_assert(i32 %c1)
  %c2 = icmp ugt i64 %2, i64 0
  call void @__VERIFIER_assert(i32 %c2)
  %3 = getelementptr { i64, i1}, { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1}, { i64, i1 }* %0
  ret { i64, i1 } %4
}
