CC = clang
CCLD = llvm-link
INC = ../../../headers
CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC)
LDFLAGS =

SOURCES = test_locks_5_safe.c \
          test_locks_6_safe.c \
          test_locks_7_safe.c \
          test_locks_8_safe.c \
          test_locks_9_safe.c \
          test_locks_10_safe.c \
          test_locks_11_safe.c \
          test_locks_12_safe.c \
          test_locks_13_safe.c \
          test_locks_14_safe.c test_locks_14_unsafe.c \
          test_locks_15_safe.c test_locks_15_unsafe.c

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

