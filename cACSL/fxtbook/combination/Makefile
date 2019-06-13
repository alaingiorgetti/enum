# File cACSL/fxtbook/combination/Makefile
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

.PHONY: compile test comb wp wa clean

%.o: %.c
	gcc -c $<

compile:
	make comb

test: compile
	./comb 4 6
	
comb: main.o comb.o ../../fcts/fcts.o
	gcc $^ -o $@
	
wp: comb.c
	frama-c -wp $< -wp-prover alt-ergo,z3 -wp-timeout 15

wa: combwa.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o comb