# File cACSL/generation/comb/Makefile

# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test comb wp clean

%.o: %.c
	gcc -c $<

compile: comb

test: compile
	./comb 4 5

comb: main.o comb.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: comb.c
	frama-c -wp $< -wp-prover alt-ergo,cvc4

clean:
	rm -f *.o comb

