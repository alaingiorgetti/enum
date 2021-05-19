######################################################################
# Copyright (C) 2019-2021 Alain Giorgetti and Clotilde Erard         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File : ptrWhy3/barray/Makefile

DIRS?= -L . -L ..

.PHONY: ide prove replay extract clean

ide:
	why3 ide $(DIRS) Barray.mlw

prove:
	why3 prove -P cvc4 -P z3 $(DIRS) Barray.mlw

replay:
	why3 replay  $(DIRS) Barray

extract:
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/barray/barray.c Barray.Barray
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/barray/enum.c Barray.Enum

clean:
	rm -f *.bak; cd Barray; rm -f *.bak
