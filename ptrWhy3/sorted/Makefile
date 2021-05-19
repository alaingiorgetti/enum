######################################################################
# Copyright (C) 2019-2021 Alain Giorgetti and Clotilde Erard         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File ptrWhy3/sorted/Makefile

DIRS?= -L . -L .. -L ../barray

.PHONY: ide replay extract clean

ide:
	why3 ide $(DIRS) Sorted.mlw

replay:
	why3 replay $(DIRS) Sorted

extract:
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/sorted/sorted.c Sorted.Sorted
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/sorted/enum.c Sorted.Enum

clean:
	rm -f *.bak; cd Sorted; rm -f *.bak
