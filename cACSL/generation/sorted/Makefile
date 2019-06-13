# File cACSL/generation/sorted/Makefile

# Run
#  make wp
# or
#  make wa
# for proving,
#  make compile
# to produce the executable and
#  make test
# for testing.

.PHONY: compile test sorted wp wa clean

%.o: %.c
	gcc -c $<

compile:
	make sorted

test: compile
	./sorted 4 3

sorted: main.o sorted.o ../../fcts/fcts.o
	gcc $^ -o $@

wp: sorted.c
	frama-c -wp sorted.c -wp-prover alt-ergo

wa: sortedwa.c
	frama-c -wp sortedwa.c -wp-prover alt-ergo

clean:
	rm -f *.o sorted
