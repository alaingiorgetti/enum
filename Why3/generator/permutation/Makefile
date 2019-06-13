#######################################################################
# Copyright 2018-19 Alain Giorgetti, Rémi Lazarini and Clotilde Erard #
# FEMTO-ST institute                                                  #
#######################################################################

#######################################################################
#  This software is distributed under the terms of the GNU Lesser     #
#  General Public License version 2.1                                 #
#######################################################################

# Why3/generator/permutation/Makefile

# Used file path list
DIRS?= -L .. -L ../..

.PHONY: test run ide replay extract clean

test:
	@echo "1. Boolean function b_permut is sound?"
	@bash ../../bet.sh "$(DIRS)" Permutation.mlw Permutation__PermutationSound.test_b_permut
	@echo "2. The reverse of a permutation is a permutation?"
	@bash ../../bet.sh "$(DIRS)" Permutation.mlw Permutation__PermutationSound.test
	@echo "3. Boolean function b_range_wrong is sound?"
	@bash ../../bet.sh "$(DIRS)" Permutation.mlw Permutation__PermutationSound.test1

run:
	why3 execute $(DIRS) Permutation.mlw Test.run

ide:
	why3 ide $(DIRS) Permutation.mlw

replay:
	why3 replay $(DIRS) Permutation

# Extract WhyML code to OCaml. Folder OCaml/generator/permutation is assumed to exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/permutation Permutation.mlw

clean:
	rm -f *.bak; rm -rf OCaml; cd Permutation; rm -f *.bak
