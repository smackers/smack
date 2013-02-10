CC = gcc
CFLAGS = -c -Wall

llvm: CC = clang
llvm: CFLAGS = -c -Wall -emit-llvm -O0

SOURCES = smack.c
OBJECTS = $(SOURCES:.c=.o)

all llvm: $(SOURCES) $(OBJECTS)

.c.o:
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.o

