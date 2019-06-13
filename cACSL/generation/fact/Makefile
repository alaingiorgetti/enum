# File cACSL/generation/fact/Makefile

# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test fact wp clean

%.o: %.c
	gcc -c $<

compile:
	make fact

test: compile
	./fact 4

fact: main.o fact.o ../../fcts/fcts.o
	gcc $^ -o $@
	
wp: fact.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o fact
