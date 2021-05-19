######################################################################
# Copyright (C) 2019-21 Alain Giorgetti and Jérome Ricciardi         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/generator/Makefile

DIRS?= -L ..

.PHONY: ide prove replay test filter run extract clean

ide:
	why3 ide $(DIRS) lexgen.mlw
	why3 ide $(DIRS) lexgenList.mlw

prove:
	why3 prove -P alt-ergo $(DIRS) lexgen.mlw
	why3 prove -P alt-ergo $(DIRS) lexgenList.mlw
	# cd barray; make prove
	# cd endo; make prove
	cd fact; make prove
	cd filtering; make prove
	cd surj; make prove

replay:
	cd barray; make replay
	cd blist; make replay
	cd endo; make replay
	cd fact; make replay
	cd filtering; make replay
	cd permutation; make replay
	cd rgf; make replay
	cd sorted; make replay
	cd surj; make replay

filter:
	cd fact; make filter
	cd rgf; make filter
	cd sorted; make filter
	cd surj; make filter

run:
	cd barray; make run
	cd blist; make run
	cd endo; make run
	cd fact; make run
	cd filtering; make run
	cd permutation; make run
	cd rgf; make run
	cd sorted; make run

extract:
	cd barray; make extract
	cd blist; make extract
	cd endo; make extract
	cd fact; make extract
	cd filtering; make extract
	cd permutation; make extract
	cd rgf; make extract
	cd sorted; make extract
	cd surj; make extract

clean:
	rm -f *.bak; cd lexgen; rm -f *.bak
	cd barray; make clean
	cd blist; make clean
	cd endo; make clean
	cd fact; make clean
	cd filtering; make clean
	cd permutation; make clean
	cd rgf; make clean
	cd sorted; make clean
	cd surj; make clean
