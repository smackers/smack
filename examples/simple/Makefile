CC = clang
INC = ../../share/smack/include
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = simple.c

BITCODE = $(SOURCES:.c=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

