######################################################################
# Copyright (C) 2019-2021 Clotilde Erard and Alain Giorgetti         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File ptrWhy3/fact/Makefile

DIRS?= -L . -L ..

.PHONY: ide prove replay extract clean

ide:
	why3 ide $(DIRS) Fact.mlw

# Known to fail: one proof requires Auto Level 3
prove:
	why3 prove -P alt-ergo -P z3 $(DIRS) Fact.mlw

replay:
	why3 replay $(DIRS) Fact

extract:
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/fact/fact.c Fact.Fact
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/fact/enum.c Fact.Enum

clean:
	rm -f *.bak; cd Fact; rm -f *.bak
