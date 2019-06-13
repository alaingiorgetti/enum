# File cACSL/generation/surjEndo/makefile
#
# Run
#  make wp
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test surjEndo wp clean

%.o: %.c
	gcc -c $<

compile:
	make surjEndo

test: compile
	./surjEndo 4

surjEndo: main.o surjEndo.o ../endobarray/endobarray.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: surjEndo.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o surjEndo
