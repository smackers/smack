# Set this variable to point to folder share of your SMACK installation
INSTALL_SHARE = ../../../install/share

CC = clang-14
LD = llvm-link-14
INC = $(INSTALL_SHARE)/smack/include
CFLAGS = -c -Wall -emit-llvm -O0 -g -Xclang -disable-O0-optnone \
	-fsanitize=signed-integer-overflow,shift -I$(INC)

SOURCES = incr.c simple.c
OBJS = $(subst .c,.bc,$(SOURCES))

all: $(OBJS)
	$(LD) -o simple-project.bc $(OBJS)

simple.bc: simple.c simple.h
incr.bc: incr.c incr.h

%.bc: %.c
	$(CC) $(CFLAGS) $< -o $@

clean:
	rm -f *.bc *.bpl
