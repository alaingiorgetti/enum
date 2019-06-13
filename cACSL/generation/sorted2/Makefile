# File cACSL/generation/sorted2/Makefile
#
# Run
#  make wp
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test sorted2 wp clean

%.o: %.c
	gcc -c $<

compile:
	make sorted2

test: compile
	./sorted2 4 3

sorted2: main.o sorted2.o ../barray/barray.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: sorted2.c
	frama-c -wp $< -wp-prover alt-ergo 

clean:
	rm -f *.o sorted2
