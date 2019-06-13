# File: cACSL/fxtbook/involution/Makefile
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
	./invol 6

invol: main.o invol.o ../../fcts/fcts.o
	gcc $^ -o $@

wp:
	frama-c -wp invol.c -wp-prover alt-ergo,cvc3

clean:
	rm -f *.o invol

