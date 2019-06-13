#!/bin/bash

# Creation script for the Docker container with Frama-C

# Get the working directory:
_pwd="$(pwd)"

docker create -ti -e DISPLAY=$DISPLAY -v /tmp/.X11-unix:/tmp/.X11-unix \
 -v ${_pwd}/fcts:/home/opam/fcts \
 -v ${_pwd}/fxtbook:/home/opam/fxtbook \
 -v ${_pwd}/generation:/home/opam/generation \
 -v ${_pwd}/global.h:/home/opam/global.h \
 -v ${_pwd}/Makefile2:/home/opam/Makefile \
 --name="framactr" frama:latest
