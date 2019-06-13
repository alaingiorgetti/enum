# File cACSL/fxtbook/permutation/Makefile

# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test perm wp wa clean

%.o: %.c
	gcc -c $<

compile:
	make perm

test: compile
	./perm 6

perm: main.o perm.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: perm.c
	frama-c -wp $< -wp-prover alt-ergo,cvc4

wa: permwa.c
	frama-c -wp $< -wp-prover alt-ergo,cvc4

clean:
	rm -f *.o perm
