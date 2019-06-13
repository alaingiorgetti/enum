# File cACSL/generation/perm/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

%.o: %.c
	gcc -c $<

compile:
	make perm

test: compile
	./perm 4

perm: main.o perm.o ../endobarray/endobarray.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: perm.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o perm
