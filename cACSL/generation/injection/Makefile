# File cACSL/generation/injection/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test inj wp clean

%.o: %.c
	gcc -c $<

compile:
	make inj

test: compile
	./inj 3 4

inj: main.o inj.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: inj.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o inj
