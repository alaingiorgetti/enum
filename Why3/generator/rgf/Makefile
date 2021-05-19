######################################################################
# Copyright 2018-2021 Clotilde Erard and Alain Giorgetti             #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/rgf/Makefile

# Used file path list
DIRS?= -L .. -L ../.. -L ../endo

.PHONY: filter run ide replay extract clean

filter:
	why3 execute $(DIRS) Rgf.mlw --use=FilterDemo 'run ()'

run:
	why3 execute $(DIRS) Rgf.mlw --use=Test 'run ()'

ide:
	why3 ide $(DIRS) Rgf.mlw

replay:
	why3 replay $(DIRS) Rgf

# Extract WhyML code to OCaml. Folder /enum/OCaml/generator/rgf is assumed to exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/rgf Rgf.mlw

clean:
	rm -f *.bak; rm -rf OCaml; cd Rgf; rm -f *.bak
