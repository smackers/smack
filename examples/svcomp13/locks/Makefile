CC = clang
INC = ../../../include
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

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

BITCODE = $(SOURCES:.c=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

