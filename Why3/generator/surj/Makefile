######################################################################
#  Copyright (C) 2019-2021 Alain Giorgetti, Clotile Erard and        #
#                                           Jérome Ricciardi         #
#  FEMTO-ST institute                                                #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/surj/Makefile

# Used file path list
DIRS?= -L .. -L ../.. -L ../barray

.PHONY: filter ide prove extract clean

filter:
	why3 execute $(DIRS) Surj.mlw --use=FilterDemo 'run ()'

ide:
	why3 ide $(DIRS) Surj.mlw

replay:
	why3 replay $(DIRS) Surj

prove:
	why3 prove -P alt-ergo $(DIRS) Surj.mlw

# Extract WhyML code to OCaml. Folder ../../../OCaml/generator/surj is assumed to pre-exist.
extract:
	why3 extract --modular --recursive -D ocaml64 $(DIRS) -o ../../../OCaml/generator/surj Surj.mlw

clean:
	rm -f *.bak; cd Surj; rm -f *.bak
