CC = clang
CCLD = llvm-link
INC = ../headers
CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC)
LDFLAGS =

SOURCES = simple.c simple_fail.c \
          simple_pre.c simple_pre_fail.c \
          simple_pre1.c simple_pre1_fail.c \
          simple_pre2.c simple_pre2_fail.c \
          simple_pre3.c simple_pre3_fail.c \
          simple_double_free.c \
          two_arrays.c \
          two_arrays1.c \
          two_arrays2.c \
          two_arrays3.c \
          two_arrays4.c \
          two_arrays5.c \
          two_arrays6.c two_arrays6_fail.c
 
OBJECTS = $(SOURCES:.c=.o)
FILES = $(basename $(SOURCES))

all: $(SOURCES) $(FILES)

$(FILES): $(OBJECTS) $(LIBS)
	$(CCLD) $(LDFLAGS) $@.o $(LIBS) -o $@

.c.o:
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.o *.bc *.bpl
	@for file in $(FILES); do \
		(rm -f $$file;) \
	done

