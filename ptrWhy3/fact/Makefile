######################################################################
# Copyright (C) 2019 Clotilde Erard and Alain Giorgetti              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File ptrWhy3/fact/Makefile

DIRS?= -L . -L ..

.PHONY: ide prove extract clean

ide:
	why3 ide $(DIRS) Fact.mlw

prove:
	why3 prove -P alt-ergo -P z3 $(DIRS) Fact.mlw

extract:
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/fact/fact.c Fact.Fact
	why3 extract --recursive -D ../cursor.drv -D c $(DIRS) -o ../../cWhy3/fact/enum.c Fact.Enum
	# Patch to remove repeated lines.
	sed '10,82d' ../../cWhy3/fact/fact.c > ../../cWhy3/fact/fact.tmp
	mv ../../cWhy3/fact/fact.tmp ../../cWhy3/fact/fact.c

clean:
	rm -f *.bak; cd Fact; rm -f *.bak
