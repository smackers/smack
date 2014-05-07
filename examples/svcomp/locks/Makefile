CC = clang
INC = ../../../include/smack
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = test_locks_5_true.c \
          test_locks_6_true.c \
          test_locks_7_true.c \
          test_locks_8_true.c \
          test_locks_9_true.c \
          test_locks_10_true.c \
          test_locks_11_true.c \
          test_locks_12_true.c \
          test_locks_13_true.c \
          test_locks_14_true.c test_locks_14_false.c \
          test_locks_15_true.c test_locks_15_false.c

BITCODE = $(SOURCES:.c=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

