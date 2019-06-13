######################################################################
# Copyright (C) 2019 Alain Giorgetti and Clotilde Erard              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/surj/Makefile

# Used file path list
DIRS?= -L .. -L ../.. -L ../barray

.PHONY: filter ide prove extract clean

filter:
	why3 execute $(DIRS) Surj.mlw FilterDemo.run

ide:
	why3 ide $(DIRS) Surj.mlw

prove:
	why3 prove -P alt-ergo $(DIRS) Surj.mlw

clean:
	rm -f *.bak; cd Surj; rm -f *.bak
