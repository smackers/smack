# Set this variable to point to folder share of your SMACK installation
INSTALL_SHARE = ../../../install/share

CC = clang
LD = llvm-link
INC = $(INSTALL_SHARE)/smack/include
CFLAGS = -c -Wall -emit-llvm -O0 -g -I$(INC)

SOURCES = incr.c simple.c
OBJS = $(subst .c,.bc,$(SOURCES)) smack.bc

all: $(OBJS)
	$(LD) -o simple-project.bc $(OBJS)

# BITPRECISE has to be set during compilation to enable bit-precise mode
bitprecise: CFLAGS = -DBITPRECISE -c -Wall -emit-llvm -O0 -g -I$(INC)
bitprecise: $(OBJS)
	$(LD) -o simple-project.bc $(OBJS)

simple.bc: simple.c simple.h
incr.bc: incr.c incr.h

smack.bc: $(INSTALL_SHARE)/smack/lib/smack.c $(INC)/smack.h
	$(CC) $(CFLAGS) $< -o smack.bc

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl

