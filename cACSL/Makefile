###################################################################
# Copyright (C) 2019 Alain Giorgetti and Clotilde Erard           #
# FEMTO-ST institute                                              #
###################################################################

###################################################################
#  This software is distributed under the terms of the GNU Lesser #
#  General Public License version 2.1                             #
###################################################################

# File: cACSL/Makefile

# Run
#  make build
# to build a docker image,
#  make ctr
# to create the Docker container, and
#  make start
# to start an interactive session in the Docker container

.PHONY: build ctr start

build: Dockerfile
	docker build --tag frama:latest .

# If 'make ctr' does not work then run 'bash ./fctr.sh' directly
ctr:
	# Uncomment next line if the container already exists
	# docker container rm framactr
	bash ./fctr.sh

# If 'make ctrmac' does not work then run 'bash ./fctrmac.sh' directly
ctrmac:
	# Uncomment next line if the container already exists
	# docker container rm framactr
	bash ./fctrmac.sh

start:
	docker start --attach --interactive framactr


