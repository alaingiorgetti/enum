#######################################################################
# Copyright 2018-19 Alain Giorgetti and Rémi Lazarini                 #
# FEMTO-ST institute                                                  #
#######################################################################

#######################################################################
#  This software is distributed under the terms of the GNU Lesser     #
#  General Public License version 2.1                                 #
#######################################################################

# Why3/generator/fact/Makefile

DIRS?= -L .. -L ../..  -L ../endo

.PHONY: test filter run ide prove extract clean

test:
	@echo "WARNING: Works only with the provided Dockerfile\n"
	@echo "1. Boolean function b_fact is sound?"
	@bash ../../bet.sh "$(DIRS)" Fact.mlw Fact__FactSound.test_b_fact

filter:
	why3 execute $(DIRS) Fact.mlw FilterDemo.run
	
run: 
	why3 execute $(DIRS) Fact.mlw Test.run

ide:
	why3 ide $(DIRS) Fact.mlw

prove: 
	why3 prove -P alt-ergo $(DIRS) Fact.mlw


# Extract WhyML code to OCaml. Folder OCaml/generator/fact is assumed to exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/fact Fact.mlw

clean:
	rm -f *.bak; rm -rf OCaml; cd Fact; rm -f *.bak
