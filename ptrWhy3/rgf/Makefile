######################################################################
# Copyright (C) 2019-2021 Clotilde Erard and Alain Giorgetti         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File ptrWhy3/rgf/Makefile

DIRS?= -L . -L ..

.PHONY: ide replay extract clean

ide:
	why3 ide $(DIRS) Rgf.mlw

replay:
	why3 replay $(DIRS) Rgf

extract:
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/rgf/rgf.c Rgf.Rgf
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/rgf/enum.c Rgf.Enum

clean:
	rm -f *.bak; cd Rgf; rm -f *.bak
