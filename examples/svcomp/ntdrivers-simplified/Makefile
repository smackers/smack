CC = clang
INC = ../../../include/smack
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = cdaudio_simpl1_true.cil.c \
          cdaudio_simpl1_false.cil.c \
          diskperf_simpl1_true.cil.c \
          floppy_simpl3_true.cil.c \
          floppy_simpl3_false.cil.c \
          floppy_simpl4_true.cil.c \
          floppy_simpl4_false.cil.c \
          kbfiltr_simpl1_true.cil.c \
          kbfiltr_simpl2_true.cil.c \
          kbfiltr_simpl2_false.cil.c \

BITCODE = $(SOURCES:.c=.bc)

all: $(BITCODE)

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

