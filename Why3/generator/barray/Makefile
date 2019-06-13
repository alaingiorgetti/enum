######################################################################
# Copyright 2018-19 Alain Giorgetti, C. Erard and R. Lazarini        #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/barray/Makefile

DIRS?= -L .. -L ../..

.PHONY: test run ide prove extract clean

test:
	@echo "1. Boolean function b_barray is sound?"
	@bash ../../bet.sh "$(DIRS)" Barray.mlw Barray__BarraySound.test_b_barray

run:
	why3 execute $(DIRS) Barray.mlw Test.run

ide:
	why3 ide $(DIRS) Barray.mlw

prove:
	why3 prove -P alt-ergo -P cvc4 -P z3 -a split_all_full $(DIRS) Barray.mlw

# Extract WhyML code to OCaml. Folder /enum/OCaml/barray is assumed to exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/barray Barray.mlw

clean:
	rm -f *.bak; rm -rf OCaml; cd Barray; rm -f *.bak
