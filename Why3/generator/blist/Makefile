#######################################################################
# Copyright 2021 Alain Giorgetti and Jérome Ricciardi                 #
# FEMTO-ST institute                                                  #
#######################################################################

#######################################################################
#  This software is distributed under the terms of the GNU Lesser     #
#  General Public License version 2.1                                 #
#######################################################################

# Why3/generator/blist/Makefile

# Used file path list
DIRS?= -L .. -L ../.. -L ../barray

.PHONY: run ide replay extract clean

run:
	why3 execute $(DIRS) Blist.mlw --use=Test 'run ()'

ide:
#bash ./scripts/blist_ide.sh
	why3 ide $(DIRS) Blist.mlw

replay:
	why3 replay $(DIRS) Blist

# Extract WhyML code to OCaml. Folder OCaml/generator/blist is assumed to exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/blist Blist.mlw

clean:
	rm -f *.bak; rm -rf OCaml; cd Blist; rm -f *.bak
