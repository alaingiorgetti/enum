# File cACSL/generation/cperm/Makefile

# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test cperm wp clean

%.o: %.c
	gcc -c $<

compile:
	make cperm

test: compile
	./cperm 4

cperm: main.o cperm.o ../../fxtbook/permutation/perm.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: cperm.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o cperm
