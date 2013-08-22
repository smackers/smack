CC = clang
INC = ../../../include/smack
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = cdaudio_simpl1_safe.cil.c \
          cdaudio_simpl1_unsafe.cil.c \
          diskperf_simpl1_safe.cil.c \
          floppy_simpl3_safe.cil.c \
          floppy_simpl3_unsafe.cil.c \
          floppy_simpl4_safe.cil.c \
          floppy_simpl4_unsafe.cil.c \
          kbfiltr_simpl1_safe.cil.c \
          kbfiltr_simpl2_safe.cil.c \
          kbfiltr_simpl2_unsafe.cil.c \

BITCODE = $(SOURCES:.c=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

