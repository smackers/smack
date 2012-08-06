CC = gcc
CCLD = $(CC)
INC = /home/zvonimir/projects/llvm-/src/projects/smack/examples/headers
CFLAGS = -c -Wall -I$(INC)
LDFLAGS =
LIBS = /home/zvonimir/projects/llvm/src/projects/smack/examples/headers/smack.o

llvm: CC = clang
llvm: CCLD = llvm-link
llvm: INC = /home/zvonimir/projects/llvm/src/projects/smack/examples/headers
llvm: CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC)
llvm: LDFLAGS =

llvm_debug: CC = clang
llvm_debug: CCLD = llvm-link
llvm_debug: INC = /home/zvonimir/projects/llvm/src/projects/smack/examples/headers
llvm_debug: CFLAGS = -g -c -Wall -emit-llvm -O0 -I$(INC)
llvm_debug: LDFLAGS = -disable-inlining -disable-opt

infer: CC = clang
infer: CCLD = llvm-link
infer: INC = /home/zvonimir/projects/llvm/src/projects/smack/examples/headers
infer: CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC) -DINFERENCE
infer: LDFLAGS = -disable-inlining -disable-opt

types: CC = clang
types: CCLD = llvm-link
types: INC = /home/zvonimir/projects/llvm/src/projects/smack/examples/headers
types: CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC) -DCHECK_TYPES
types: LDFLAGS = -disable-inlining -disable-opt

inline: CC = clang
inline: CCLD = llvm-link
inline: INC = /home/zvonimir/projects/llvm/src/projects/smack/examples/headers
inline: CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC) -DENABLE_INLINE
inline: LDFLAGS =

SOURCES = simple.c simple_fail.c \
          pointers.c pointers1.c pointers2.c pointers3.c \
          array.c \
          array1.c array1_fail.c

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
		 smack $$file -use_dsa; \
		 echo; echo) \
	done

inference:
	@for file in $(FILES); do   \
		(echo Running SMACK on $$file ...; \
		 smack $$file -inference; \
		 echo; echo) \
	done

