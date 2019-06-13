# File cACSL/fxtbook/subset/Makefile
#
# Run
#  make wp
# or
#  make wa
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test subset wp wa clean

%.o: %.c
	gcc -c $<

compile:
	make subset

test: compile
	./subset 6

subset: main.o subset.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: subset.c
	frama-c -wp $< -wp-prover alt-ergo

wa: subsetwa.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o subset
