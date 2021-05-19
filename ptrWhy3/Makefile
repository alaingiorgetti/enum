######################################################################
# Copyright (C) 2019-2021 Clotilde Erard and Alain Giorgetti         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# ptrWhy3/Makefile

DIRS?= -L .

.PHONY: ide prove replay extract clean

ide:
	why3 ide lex.mlw
	why3 ide $(DIRS) lexgen.mlw
	why3 ide $(DIRS) arrayExtension.mlw

prove:
	why3 prove $(DIRS) -P alt-ergo arrayExtension.mlw
	why3 prove -P z3 lex.mlw
	why3 prove $(DIRS) -P alt-ergo lexgen.mlw
	cd barray; make prove

replay:
	why3 replay lex
	why3 replay $(DIRS) lexgen
	why3 replay $(DIRS) arrayExtension
	cd permutation; make replay
	cd rgf; make replay

extract:
	cd barray; make extract
	cd fact; make extract
	cd permutation; make extract
	cd rgf; make extract
	cd sorted; make extract

clean:
	rm -f *.bak
	cd arrayExtension; rm -f *.bak
	cd lex; rm -f *.bak
	cd lexgen; rm -f *.bak
	cd barray; make clean
	cd fact; make clean
	cd permutation; make clean
	cd rgf; make clean
	cd sorted; make clean
