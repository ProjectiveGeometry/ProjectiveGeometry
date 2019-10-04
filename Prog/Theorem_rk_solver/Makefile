CFLAGS = -g -Wall
IFLAGS = -Iinclude 
OPATH = obj/

vpath %.h include
vpath %.c src
vpath %.o obj
vpath main bin

all : main

main : main.o parties.o graph.o set.o maths_addon.o
	gcc $(CFLAGS) -o main $(OPATH)main.o $(OPATH)parties.o $(OPATH)graph.o $(OPATH)set.o $(OPATH)maths_addon.o -lm 
	mv $@ bin/

main.o : parties.h graph.h set.h maths_addon.h
parties.o : parties.h graph.h set.h maths_addon.h 
graph.o : set.h maths_addon.h
set.o : set.h
maths_addon.o : maths_addon.h


%.o : %.c
	gcc $(CFLAGS) -c $< $(IFLAGS)
	mv $@ $(OPATH)

geany :
	geany src/* include/* Makefile &

clean : 
	rm obj/* bin/*

archive : 
	tar -f code.tar.gz -cvz src/* include/* makefile

