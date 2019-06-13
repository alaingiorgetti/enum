#######################################################################
# Copyright 2018-19 Clotilde Erard and Alain Giorgetti                #
# FEMTO-ST institute                                                  #
#######################################################################

#######################################################################
#  This software is distributed under the terms of the GNU Lesser     #
#  General Public License version 2.1                                 #
#######################################################################

# File : cWhy3/Makefile

.PHONY: compile test clean

compile:
	cd fcts; make
	cd barray; make compile
	cd fact; make compile
	cd permutation; make compile
	cd rgf; make compile
	cd sorted; make compile

test: compile
	cd barray; make test
	cd fact; make test
	cd permutation; make test
	cd rgf; make test
	cd sorted; make test

clean:
	cd fcts; make clean
	cd barray; make clean
	cd fact; make clean
	cd permutation; make clean
	cd rgf; make clean
	cd sorted; make clean