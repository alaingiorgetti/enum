# File cACSL/generation/sorted1/Makefile
#
# Run
#  make wp
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test sorted1 wp clean

%.o: %.c
	gcc -c $<

compile:
	make sorted1

test: compile
	./sorted1 4 3

sorted1: main.o sorted1.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: sorted1.c
	frama-c -wp $< -wp-prover alt-ergo 

clean:
	rm -f *.o sorted1
