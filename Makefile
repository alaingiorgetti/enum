######################################################################
# Copyright (C) 2018-2021 Alain Giorgetti, Clotilde Erard,           #
#                         Rémi Lazarini and Jérome Ricciardi         #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# File: enum/Makefile

# Run
#   make build
# to build a docker image,
#   make ctr
# to create the Docker container,
#   make start
# to start an interactive session in the Docker container

.PHONY: build ctr start

build: Dockerfile
	docker build --tag enum:latest .

# Sometimes does not work! Then run 'bash ./ctr.sh' directly!
ctr:
	# Uncomment next line if the container already exists
	# docker container rm enumctr
	bash ./ctr.sh

# For more safety xhost is opened only to the container on the local host's docker daemon
# whose container's ID has been stored by ctr.sh to the shell variable containerId.
start:
	@xhost +local:`docker inspect --format='{{ .Config.Hostname }}' enumctr` >> /dev/null
	docker start --attach --interactive enumctr

