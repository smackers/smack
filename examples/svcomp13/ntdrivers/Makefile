CC = clang
CCLD = llvm-link
INC = ../../../headers
CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC)
LDFLAGS =

SOURCES = cdaudio_safe.i.cil.c \
          cdaudio_unsafe.i.cil.c \
          diskperf_safe.i.cil.c \
          diskperf_unsafe.i.cil.c \
          floppy2_safe.i.cil.c \
          floppy_safe.i.cil.c \
          floppy_unsafe.i.cil.c \
          kbfiltr_safe.i.cil.c.trace \
          kbfiltr_unsafe.i.cil.c \
          parport_safe.i.cil.c \
          parport_unsafe.i.cil.c

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

