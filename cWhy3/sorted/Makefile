######################################################################
# Copyright (C) 2019 Clotilde Erard and Alain Giorgetti              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File : cWhy3/sorted/Makefile

.PHONY: compile test clean

compile: ../mainInt.c enum.c sorted.c ../fcts/fcts.c
	gcc -Wall -g -pedantic $^ -Ibuild -o main

test: compile
	./main 4 3

clean:
	rm -f main
