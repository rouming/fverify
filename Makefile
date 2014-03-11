# Makefile for fverify tool

CC = $(CROSS_COMPILE)gcc
DEFINES=-D_GNU_SOURCE -D_LARGEFILE64_SOURCE -D_FILE_OFFSET_BITS=64 -D_XOPEN_SOURCE=600

CFLAGS = -std=c99 -g -Wall -Wextra $(DEFINES)

all: fverify
%: %.c
	$(CC) $(CFLAGS) -o $@ $^

clean:
	$(RM) fverify *~
