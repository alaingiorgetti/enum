#######################################################################
# Copyright (C) 2018-19 Alain Giorgetti and Clotilde Erard            #
# FEMTO-ST institute                                                  #
#######################################################################

#######################################################################
#  This software is distributed under the terms of the GNU Lesser     #
#  General Public License version 2.1                                 #
#######################################################################

# File: enum/Makefile

# Run
#  make build
# to build a docker image,
#  make ctr
# to create the Docker container,
#  make start
# to start an interactive session in the Docker container

.PHONY: build ctr start clean

build: Dockerfile
	docker build --tag enum:latest .

# Sometimes does not work! Then run 'bash ./ctr.sh' directly!
ctr:
	# Uncomment next line if the container already exists
	# docker container rm enumctr
	bash ./ctr.sh

# Sometimes does not work! Then run 'bash ./ctrmac.sh' directly!
ctrmac:
	# Uncomment next line if the container already exists
	# docker container rm enumctr
	bash ./ctrmac.sh

start:
	docker start --attach --interactive enumctr

