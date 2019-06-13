######################################################################
# Copyright (C) 2018-19 Alain Giorgetti and Rémi Lazarini            #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/Makefile

.PHONY: ide prove test filter run extract latex clean

# Set timeout to 10 seconds (File/Preferences/General/Time limit)
ide:
	why3 ide arrayExtension.mlw
	why3 ide listExtension.mlw
	why3 ide mapExtension.mlw
	why3 ide lex.mlw

prove:
	why3 prove -P alt-ergo -P z3 -a split_all_full arrayExtension.mlw
	why3 prove -P alt-ergo listExtension.mlw
	why3 prove -P alt-ergo -P z3 mapExtension.mlw
	why3 replay lex
	cd generator; make prove

test:
	cd generator; make test

filter:
	cd generator; make filter

run:
	cd generator; make run

extract:
	cd generator; make extract

latex:
	why3 session latex arrayExtension listExtension lex generator/barray/Barray \
	generator/endo/Endo generator/fact/Fact generator/filtering/Filtering \
	generator/lexgen generator/permutation/Permutation \
	generator/rgf/Rgf generator/sorted/Sorted generator/surj/Surj
	
clean:
	rm -f *.bak;
	cd arrayExtension; rm -f *.bak
	cd listExtension; rm -f *.bak
	cd mapExtension; rm -f *.bak
	cd lex; rm -f *.bak
	cd generator; make clean