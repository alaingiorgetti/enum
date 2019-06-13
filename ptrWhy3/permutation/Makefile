######################################################################
# Copyright (C) 2019 Alain Giorgetti and Clotilde Erard              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File ptrWhy3/permutation/Makefile

DIRS?= -L . -L ..

.PHONY: ide prove extract clean

ide:
	why3 ide $(DIRS) Permutation.mlw

replay:
	why3 replay $(DIRS) Permutation


extract: extract
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/permutation/perm.c Permutation.Permutation
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/permutation/enum.c Permutation.Enum
	# Patch to remove repeated lines:
	sed '10,82d' ../../cWhy3/permutation/perm.c > ../../cWhy3/permutation/perm.tmp
	mv ../../cWhy3/permutation/perm.tmp ../../cWhy3/permutation/perm.c

clean:
	rm -f *.bak; cd Permutation; rm -f *.bak
