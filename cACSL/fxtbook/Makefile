###################################################################
# Copyright (C) 2014-2019 R. Genestier, A. Giorgetti and C. Erard #
# FEMTO-ST institute                                              #
###################################################################

###################################################################
#  This software is distributed under the terms of the GNU Lesser #
#  General Public License version 2.1                             #
###################################################################

# File: cACSL/fxtbook/Makefile

# Run
#  make wp
# to prove, run
#  make compile
# to produce the executable and run
#  make test
# for testing.

# This command works only in a docker container with Frama-C
wp:
	cd combination; make wp
	cd involution; make wp
	cd permutation; make wp
	cd rgf; make wp
	cd subset; make wp

compile:
	cd ../fcts; make
	cd combination; make compile
	cd involution; make compile
	cd permutation; make compile
	cd rgf; make compile
	cd subset; make compile

test: compile
	cd combination; make test
	cd involution; make test
	cd permutation; make test
	cd rgf; make test
	cd subset; make test
	
clean:
	cd ../fcts; make clean
	cd combination; make clean
	cd involution; make clean
	cd permutation; make clean
	cd rgf; make clean
	cd subset; make clean