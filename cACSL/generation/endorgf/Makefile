# File cACSL/generation/endorgf/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test endorgf wp clean

%.o: %.c
	gcc -c $<

compile:
	make rgf

test: compile
	./rgf 4

rgf: main.o rgf.o ../endobarray/endobarray.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: rgf.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o rgf

