# File cACSL/generation/ffi/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test ffi wp clean

%.o: %.c
	gcc -c $<

compile:
	make ffi

test: compile
	./ffi 8

ffi: main.o ffi.o ../invol/invol.o ../injEndo/injEndo.o ../endobarray/endobarray.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: ffi.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o ffi
