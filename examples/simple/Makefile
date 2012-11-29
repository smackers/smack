CC = gcc
CCLD = $(CC)
INC = ../headers
CFLAGS = -c -Wall -I$(INC)
LDFLAGS =
LIBS = ../headers/smack.o

llvm: CC = clang
llvm: CCLD = llvm-link
llvm: INC = ../headers
llvm: CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC)
llvm: LDFLAGS =

llvm_debug: CC = clang
llvm_debug: CCLD = llvm-link
llvm_debug: INC = ../headers
llvm_debug: CFLAGS = -g -c -Wall -emit-llvm -O0 -I$(INC)
llvm_debug: LDFLAGS = -disable-inlining -disable-opt

infer: CC = clang
infer: CCLD = llvm-link
infer: INC = ../headers
infer: CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC) -DINFERENCE
infer: LDFLAGS = -disable-inlining -disable-opt

types: CC = clang
types: CCLD = llvm-link
types: INC = ../headers
types: CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC) -DCHECK_TYPES
types: LDFLAGS = -disable-inlining -disable-opt

inline: CC = clang
inline: CCLD = llvm-link
inline: INC = ../headers
inline: CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC) -DENABLE_INLINE
inline: LDFLAGS =

SOURCES = simple.c simple_fail.c \
          simple_double_free.c \
          simple_pre.c simple_pre_fail.c \
          simple_pre1.c simple_pre1_fail.c \
          simple_pre2.c simple_pre2_fail.c \
          simple_pre3.c simple_pre3_fail.c \
          pointers.c pointers1.c pointers2.c pointers3.c \
          nested_struct.c nested_struct_fail.c \
          nested_struct1.c nested_struct1_fail.c \
          nested_struct2.c nested_struct2_fail.c \
          array.c \
          array1.c array1_fail.c \
          array2.c array2_fail.c \
          array3.c array3_fail.c \
          array4.c array4_fail.c \
          array_free.c array_free_fail.c \
          array_free1.c array_free1_fail.c \
          array_free2.c array_free2_fail.c \
          two_arrays.c \
          two_arrays1.c \
          two_arrays2.c \
          two_arrays3.c \
          two_arrays4.c \
          two_arrays5.c \
          two_arrays6.c two_arrays6_fail.c \
          func_ptr.c \
          func_ptr1.c func_ptr1_fail.c \
          func_ptr2.c \
          func_ptr3.c \
          lock.c \
          lock1.c \
          loop.c \
          loop1.c \
          ase_example.c ase_example_fail.c \
          caduceus_example.c \
          vmcai_struct.c \
          vmcai_bytes.c

OBJECTS = $(SOURCES:.c=.o)
FILES = $(basename $(SOURCES))

all llvm llvm_debug infer types inline: $(SOURCES) $(FILES)

$(FILES): $(OBJECTS) $(LIBS)
	$(CCLD) $(LDFLAGS) $@.o $(LIBS) -o $@

.c.o:
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.o *.bc *.bpl
	@for file in $(FILES); do \
		(rm -f $$file;) \
	done

run:
	@for file in $(FILES); do   \
		(echo Running SMACK on $$file ...; \
		 smack $$file; \
		 echo; echo) \
	done

inference:
	@for file in $(FILES); do   \
		(echo Running SMACK on $$file ...; \
		 smack $$file -inference; \
		 echo; echo) \
	done

