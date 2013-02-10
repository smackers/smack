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

SOURCES = simple.c simple_fail.c \
          two_arrays.c \
          two_arrays1.c \
          two_arrays2.c \
          two_arrays3.c \
          two_arrays4.c \
          two_arrays5.c \
          two_arrays6.c two_arrays6_fail.c
 
OBJECTS = $(SOURCES:.c=.o)
FILES = $(basename $(SOURCES))

all llvm: $(SOURCES) $(FILES)

$(FILES): $(OBJECTS) $(LIBS)
	$(CCLD) $(LDFLAGS) $@.o $(LIBS) -o $@

.c.o:
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.o *.bc *.bpl
	@for file in $(FILES); do \
		(rm -f $$file;) \
	done

