######################################################################
# Copyright (C) 2019 Clotilde Erard and Alain Giorgetti              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File ptrWhy3/rgf/Makefile

DIRS?= -L . -L ..

.PHONY: ide prove extract clean

ide:
	why3 ide $(DIRS) Rgf.mlw

prove:
	why3 prove -a split_all_full -P alt-ergo -P cvc4 -P z3 $(DIRS) Rgf.mlw

extract: extract
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/rgf/rgf.c Rgf.Rgf
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/rgf/enum.c Rgf.Enum
	# Patch to remove repeated lines:
	sed '10,82d' ../../cWhy3/rgf/rgf.c > ../../cWhy3/rgf/rgf.tmp
	mv ../../cWhy3/rgf/rgf.tmp ../../cWhy3/rgf/rgf.c

clean:
	rm -f *.bak; cd Rgf; rm -f *.bak
