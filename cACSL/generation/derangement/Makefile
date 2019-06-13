# File cACSL/generation/derangement/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test derang wp clean

%.o: %.c
	gcc -c $<

compile:
	make derang

test: compile
	./derang 4

derang: main.o derang.o ../injEndo/injEndo.o ../endobarray/endobarray.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: derang.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o derang

