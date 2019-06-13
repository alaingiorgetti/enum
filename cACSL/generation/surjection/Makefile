# File cACSL/generation/surjection/Makefile
#
# Run
#  make wp
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test surj wp clean

%.o: %.c
	gcc -c $<

compile:
	make surj

test: compile
	./surj 4 3

surj: main.o surj.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: surj.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o surj
