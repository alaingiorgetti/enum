# File cACSL/generation/endoinj/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test endoinj wp clean

%.o: %.c
	gcc -c $<

compile:
	make endoinj

test: compile
	./endoinj 4

endoinj: main.o endoinj.o ../injection/inj.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: endoinj.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o endoinj
