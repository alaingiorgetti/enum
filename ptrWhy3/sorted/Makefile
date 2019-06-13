######################################################################
# Copyright (C) 2019 Alain Giorgetti and Clotilde Erard              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File ptrWhy3/sorted/Makefile

DIRS?= -L . -L .. -L ../barray

.PHONY: ide prove extract clean

ide:
	why3 ide $(DIRS) Sorted.mlw

prove:
	why3 prove -P alt-ergo -P z3 $(DIRS) Sorted.mlw

extract:
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/sorted/sorted.c Sorted.Sorted
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/sorted/enum.c Sorted.Enum
	# Patch to remove repeated lines:
	sed '10,82d' ../../cWhy3/sorted/sorted.c > ../../cWhy3/sorted/sorted.tmp
	mv ../../cWhy3/sorted/sorted.tmp ../../cWhy3/sorted/sorted.c

clean:
	rm -f *.bak; cd Sorted; rm -f *.bak
