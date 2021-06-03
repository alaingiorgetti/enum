######################################################################
# Copyright (C) 2019-2021 Alain Giorgetti and Clotilde Erard         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File ptrWhy3/permutation/Makefile

DIRS?= -L . -L ..

.PHONY: ide replay extract clean

ide:
	why3 ide $(DIRS) Permutation.mlw

replay:
	why3 replay $(DIRS) Permutation

extract:
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/permutation/perm.c Permutation.Permutation
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/permutation/enum.c Permutation.Enum

clean:
	rm -f *.bak; cd Permutation; rm -f *.bak
