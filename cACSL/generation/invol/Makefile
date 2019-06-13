# File cACSL/generation/invol/Makefile
#
# Run
#  make wp
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test invol wp clean

%.o: %.c
	gcc -c $<

compile:
	make invol

test: compile
	./invol 4

invol: main.o invol.o ../injEndo/injEndo.o ../endobarray/endobarray.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: invol.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o invol

