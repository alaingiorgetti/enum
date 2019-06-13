# File cACSL/generation/endobarray/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test endobarray wp clean

%.o: %.c
	gcc -c $<

compile:
	make endobarray

test: compile
	./endobarray 4

endobarray: main.o endobarray.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: endobarray.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o endobarray
