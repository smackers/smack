CC = clang
INC = ../include
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = smack.c pthread.c

BITCODE = $(SOURCES:.c=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc

