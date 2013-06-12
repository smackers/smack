CC = clang
CCLD = llvm-link
INC = ../../../headers
CFLAGS = -c -Wall -emit-llvm -O0 -I$(INC)
LDFLAGS =

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

