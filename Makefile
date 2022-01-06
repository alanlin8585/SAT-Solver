# A template C++ Makefile for your SAT solver.

# Debugging flags
#FLAGS=-Wall -Wold-style-cast -Wformat=2 -ansi -pedantic -ggdb3 -DDEBUG

FLAGS=-Wall -Wformat=2 -pedantic -O3 -std=c++14
OBJS=parser.o sat.o
EXENAME=yasat

all: $(OBJS)
	g++ $(FLAGS) $(OBJS) -lz -o $(EXENAME)
parser.o: parser.cpp parser.h
	g++ $(FLAGS) -c parser.cpp
sat.o: sat.cpp parser.h sat.hpp
	g++ $(FLAGS) -c sat.cpp

.PHONY: clean
clean:
	rm -rf $(OBJS) $(EXENAME)
