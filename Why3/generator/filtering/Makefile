######################################################################
# Copyright (C) 2019 Alain Giorgetti and Clotilde Erard              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/filtering/Makefile

# Used file path list
DIRS?= -L .. -L ../.. -L ../barray

.PHONY: run ide prove extract clean

run:
	why3 execute $(DIRS) Filtering.mlw --use=FilterDemoInj 'run ()'
	why3 execute $(DIRS) Filtering.mlw --use=FilterDemoComb 'run ()'

ide:
	why3 ide $(DIRS) Filtering.mlw

replay:
	why3 replay $(DIRS) Filtering

prove:
	why3 prove -P alt-ergo $(DIRS) Filtering.mlw

# Extract WhyML code to OCaml. Folder ../../../OCaml/generator/filtering is assumed to pre-exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/filtering Filtering.mlw

clean:
	rm -f *.bak; cd Filtering; rm -f *.bak
