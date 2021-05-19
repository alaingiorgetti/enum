######################################################################
# Copyright (C) 2018-2021 Alain Giorgetti, Clotilde Erard,           #
#                         Rémi Lazarini and Jérome Ricciardi         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/barray/Makefile

DIRS?= -L .. -L ../..

.PHONY: run ide replay prove extract clean

run:
	why3 execute $(DIRS) Barray.mlw --use=Test 'run ()'

ide:
	why3 ide $(DIRS) Barray.mlw

replay:
	why3 replay $(DIRS) Barray

prove:
	why3 prove -P alt-ergo -P cvc4 -P z3 -a split_all_full $(DIRS) Barray.mlw

# Extract WhyML code to OCaml. Folder /enum/OCaml/generator/barray is assumed to exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/barray Barray.mlw

clean:
	rm -f *.bak; rm -rf OCaml; cd Barray; rm -f *.bak
