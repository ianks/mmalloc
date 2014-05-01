#
# Students' Makefile for the Malloc Lab
#
TEAM = xyzzy
VERSION = 1

CC = gcc
CFLAGS = -g -Wall -O2 -m32

OBJS = mdriver.o mm.o memlib.o fsecs.o fcyc.o clock.o ftimer.o
DBUG = mm.o memlib.o

mdriver: $(OBJS)
	$(CC) $(CFLAGS) -o mdriver $(OBJS)

debug: $(DBUG) 
	$(CC) $(CFLAGS) -o debug $(DBUG)

test: test
	./mdriver -V -t traces

mdriver.o: mdriver.c fsecs.h fcyc.h clock.h memlib.h config.h mm.h
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h
fsecs.o: fsecs.c fsecs.h config.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h
debug.o: debug.c

clean:
	rm -f *~ *.o mdriver


