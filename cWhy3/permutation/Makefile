######################################################################
# Copyright (C) 2019 Alain Giorgetti and Clotilde Erard              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File : cWhy3/permutation/Makefile

.PHONY: compile test clean

compile: ../main.c enum.c perm.c ../fcts/fcts.c
	gcc -Wall -g -pedantic $^ -Ibuild -o main

test: compile
	./main 4

clean:
	rm -f main
