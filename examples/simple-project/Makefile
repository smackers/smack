CC = clang
LD = llvm-link
INC = ../../../install/share/include
LDLIBS = ../../../install/share/lib/smack-defs.bc
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = incr.c simple.c
OBJS = $(subst .c,.bc,$(SOURCES))

all: $(OBJS)
	$(LD) -o simple-project.bc $(OBJS) $(LDLIBS)

simple.bc: simple.c simple.h
incr.bc: incr.c incr.h

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

