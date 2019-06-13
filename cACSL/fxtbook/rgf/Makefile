# File cACSL/fxtbook/rgf/Makefile

# Run
#  make wp
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test rgf wp wa clean

%.o: %.c
	gcc -c $<

compile:
	make rgf

test: compile
	./rgf 6

rgf: main.o rgf.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: rgf.c
	frama-c -wp $< -wp-prover alt-ergo,z3

wa: rgfwa.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o rgf
