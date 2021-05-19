######################################################################
#  Copyright (C) 2018-2021 Alain Giorgetti, Rémi Lazarini and        #
#                                           Jérome Ricciardi         #
#  FEMTO-ST institute                                                #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Why3/Makefile

.PHONY: ide prove test filter run extract latex clean

# Set timeout to 10 seconds (File/Preferences/General/Time limit)

all: prove filter run extract clean

ide:
	why3 ide arrayExtension.mlw
	why3 ide listExtension.mlw
	why3 ide mapExtension.mlw
	why3 ide lex.mlw
	why3 ide lexList.mlw

prove:
	why3 prove -P cvc4 arrayExtension.mlw -T Array -G "copy'vc"
	why3 prove -P cvc4 arrayExtension.mlw -T ArrayInjection -G injective_surjective -G injection_occ -G "b_diff'vc" -G "b_range'vc" 
	# why3 prove -P z3 arrayExtension.mlw -T ArrayInjection -G "b_inj'vc"
	# TODO: find out how to use a specific version of prover.
	# why3 prove -P Z3 4.7.1 arrayExtension.mlw -a split_vc -T ArrayInjection -G endoinjection_occ
	why3 prove -P cvc4 listExtension.mlw
	why3 prove -P cvc4 -P z3 mapExtension.mlw
	why3 prove -P alt-ergo lex.mlw
	why3 prove -P cvc4 lexList.mlw
	# TODO: resume the 'make prove' of all generators.
	#cd generator; make prove

replay:
	why3 replay arrayExtension
	why3 replay listExtension
	why3 replay mapExtension
	why3 replay lex
	why3 replay lexList
	cd generator; make replay

filter:
	cd generator; make filter

run:
	cd generator; make run

extract:
	cd generator; make extract

# Only in the Docker container:
latex:
	why3 session latex arrayExtension listExtension lex lexList \
	generator/lexgen generator/lexgenList \
	generator/barray/Barray \
	generator/endo/Endo generator/fact/Fact generator/filtering/Filtering \
	generator/permutation/Permutation \
	generator/rgf/Rgf generator/sorted/Sorted generator/surj/Surj

html:
	why3 session html arrayExtension listExtension lex lexList \
	generator/lexgen generator/lexgenList \
	generator/barray/Barray \
	generator/endo/Endo generator/fact/Fact \
	generator/filtering/Filtering \
	generator/permutation/Permutation \
	generator/rgf/Rgf \
	generator/sorted/Sorted generator/surj/Surj

clean:
	rm -f *.bak;
	cd arrayExtension; rm -f *.bak
	cd lex; rm -f *.bak
	cd lexList; rm -f *.bak
	cd listExtension; rm -f *.bak
	cd mapExtension; rm -f *.bak
	cd generator; make clean
	cd ../OCaml; make clean