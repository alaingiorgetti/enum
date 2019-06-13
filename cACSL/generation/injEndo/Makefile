# File cACSL/generation/injEndo/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test injEndo wp clean

%.o: %.c
	gcc -c $<

compile:
	make injEndo

test: compile
	./injEndo 4

injEndo: main.o injEndo.o ../endobarray/endobarray.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: injEndo.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o injEndo
