CC = clang
CPP = clang++
INC = ../include/smack
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = hello.cc hello_fail.cc \
          simple.c simple_fail.c \
          simple_pre.c simple_pre_fail.c \
          simple_pre1.c simple_pre1_fail.c \
          simple_pre2.c simple_pre2_fail.c \
          simple_pre3.c simple_pre3_fail.c \
          simple_double_free.c \
          pointers.c pointers_fail.c \
          pointers1.c pointers1_fail.c \
          pointers2.c pointers2_fail.c \
          pointers3.c pointers3_fail.c \
          globals.c globals_fail.c \
          loop.c loop_fail.c \
          loop1.c loop1_fail.c \
          nondet.c \
          printfs.c \
          struct_return.c \
          struct_init.c struct_init_fail.c \
          extern_struct.c \
          extern_func.c \
          extern_mem.c extern_mem_fail.c \
          smack_code_call.c smack_code_call_fail.c \
          return_label.c \
          struct_cast.c struct_cast_fail.c \
          struct_cast1.c struct_cast1_fail.c \
          nested_struct.c nested_struct_fail.c \
          nested_struct1.c nested_struct1_fail.c \
          nested_struct2.c nested_struct2_fail.c \
          struct_assign.c struct_assign_fail.c \
          func_ptr.c func_ptr_fail.c \
          func_ptr1.c func_ptr1_fail.c \
          array.c \
          array1.c array1_fail.c \
          array2.c array2_fail.c \
          array3.c array3_fail.c \
          array4.c array4_fail.c \
          array_free.c array_free_fail.c \
          array_free1.c array_free1_fail.c \
          array_free2.c array_free2_fail.c \
          lock.c lock_fail.c \
          ase_example.c ase_example_fail.c \
          two_arrays.c \
          two_arrays1.c \
          two_arrays2.c \
          two_arrays3.c \
          two_arrays4.c \
          two_arrays5.c \
          two_arrays6.c two_arrays6_fail.c \
					floats_in_memory.c floats_in_memory_fail.c

BITCODE = $(SOURCES:.c=.bc) $(SOURCES:.cc=.bc) $(SOURCES:.cpp=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

%.bc: %.cc
	$(CPP) $(CFLAGS) $< -o $@

%.bc: %.cpp
	$(CPP) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

