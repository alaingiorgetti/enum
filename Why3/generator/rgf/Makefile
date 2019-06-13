######################################################################
# Copyright 2018-19 Clotilde Erard and Alain Giorgetti               #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/rgf/Makefile

# Used file path list
DIRS?= -L .. -L ../.. -L ../endo

.PHONY: test filter run ide prove extract clean

test:
	@echo "1. Boolean function b_rgf is sound?"
	@bash ../../bet.sh "$(DIRS)" Rgf.mlw Rgf__RgfSound.test_b_rgf

filter:
	why3 execute $(DIRS) Rgf.mlw FilterDemo.run

run:
	why3 execute $(DIRS) Rgf.mlw Test.run

ide:
	why3 ide $(DIRS) Rgf.mlw

prove:
	why3 prove -P alt-ergo -P z3 -t 10 -a split_vc $(DIRS) Rgf.mlw

replay:
	why3 replay $(DIRS) Rgf

# Extract WhyML code to OCaml. Folder /enum/OCaml/rgf is assumed to exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/rgf Rgf.mlw

clean:
	rm -f *.bak; rm -rf OCaml; cd Rgf; rm -f *.bak
