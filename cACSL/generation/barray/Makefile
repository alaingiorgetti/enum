# File cACSL/generation/barray/Makefile

# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test barray wp clean

%.o: %.c
	gcc -c $<

compile:
	make barray

test: compile
	./barray 4 3

barray: main.o barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: barray.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o barray
