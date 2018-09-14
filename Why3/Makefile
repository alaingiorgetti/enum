######################################################################
# Copyright 2018 Alain Giorgetti and Rémi Lazarini                   #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

.PHONY: idebarray idepermut idepermut1 build start

# start why3 ide with Barray.mlw
idebarray:
	why3 ide -L ./ Barray.mlw

# start why3 ide with Permutation.mlw
idepermut:
	why3 ide -L ./ Permutation.mlw

# start why3 ide with Permutation.mlw
idepermut1:
	why3 ide -L ./ Permutation1.mlw

build:
	docker build --tag proofimg .

start:
	docker start --attach --interactive proofctr
