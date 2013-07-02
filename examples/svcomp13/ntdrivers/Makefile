CC = clang
INC = ../../../headers
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = cdaudio_safe.i.cil.c \
          cdaudio_unsafe.i.cil.c \
          diskperf_safe.i.cil.c \
          diskperf_unsafe.i.cil.c \
          floppy2_safe.i.cil.c \
          floppy_safe.i.cil.c \
          floppy_unsafe.i.cil.c \
          kbfiltr_unsafe.i.cil.c \
          parport_safe.i.cil.c \
          parport_unsafe.i.cil.c

BITCODE = $(SOURCES:.c=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

