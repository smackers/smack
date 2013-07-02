CC = clang
CFLAGS = -c -Wall -emit-llvm -O0 -g

SOURCES = smack.c
OBJECTS = $(SOURCES:.c=.o)

all: $(SOURCES) $(OBJECTS)

.c.o:
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.o

