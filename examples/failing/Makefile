CC = clang
CCLD = llvm-link
INC = ../../headers
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)
LDFLAGS =

SOURCES = globals_func_ptr.c

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

