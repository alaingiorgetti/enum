######################################################################
# Copyright (C) 2018-19 Clotilde Erard                               #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/sorted/Makefile

# Used file path list
DIRS?= -L .. -L ../.. -L ../barray

.PHONY: test filter run ide prove extract clean

test:
	@echo "1. Boolean function b_sorted is sound?"
	@bash ../../bet.sh "$(DIRS)" Sorted.mlw Sorted__SortedSound.test_b_sorted

filter:
	why3 execute $(DIRS) Sorted.mlw FilterDemo.run

run:
	why3 execute $(DIRS) Sorted.mlw Test.run

ide:
	why3 ide $(DIRS) Sorted.mlw

replay:
	why3 replay $(DIRS) Sorted

# Extract WhyML code to OCaml. Folder /enum/OCaml/sorted is assumed to exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/sorted Sorted.mlw

clean:
	rm -f *.bak; rm -rf OCaml; cd Sorted; rm -f *.bak
