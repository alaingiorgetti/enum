# File cACSL/generation/endosurj/Makefile
#
# Run
#  make wp 
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test endosurj wp clean

%.o: %.c
	gcc -c $<

compile:
	make endosurj

test: compile
	./endosurj 4

endosurj: main.o endosurj.o ../surjection/surj.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: endosurj.c
	frama-c -wp $< -wp-prover alt-ergo

clean:
	rm -f *.o endosurj
