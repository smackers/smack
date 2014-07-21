CC = clang
INC = ../../../include/smack
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = cdaudio_true.i.cil.c \
          diskperf_true.i.cil.c \
          diskperf_false.i.cil.c \
          floppy2_true.i.cil.c \
          floppy_true.i.cil.c \
          floppy_false.i.cil.c \
          kbfiltr_false.i.cil.c \
          parport_true.i.cil.c \
          parport_false.i.cil.c

BITCODE = $(SOURCES:.c=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

