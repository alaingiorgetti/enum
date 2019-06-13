######################################################################
# Copyright (C) 2019 Alain Giorgetti and Clotilde Erard              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/endo/Makefile

# Used file path list
DIRS?= -L .. -L ../..

.PHONY: test run ide prove extract clean

test:
	@echo "WARNING: Works only with the provided Dockerfile\n"
	@echo "1. Boolean function b_endo is sound?"
	@bash ../../bet.sh "$(DIRS)" Endo.mlw Endo__EndoSound.test_b_endo

run:
	why3 execute $(DIRS) Endo.mlw Test.run

ide:
	why3 ide $(DIRS) Endo.mlw

prove:
	why3 prove -P alt-ergo $(DIRS) Endo.mlw

# Extract WhyML code to OCaml. Folder ../../../OCaml/generator/endo is assumed to pre-exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/endo Endo.mlw

clean:
	rm -f *.bak; rm -rf OCaml; rm -rf _build; cd Endo; rm -f *.bak
