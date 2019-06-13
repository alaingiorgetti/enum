#!/bin/bash

# Creation script for the Docker container

# Get the working directory:
_pwd="$(pwd)"

docker create -ti -e DISPLAY=docker.for.mac.host.internal:0 \
 -v ${_pwd}/cACSL:/home/opam/enum/cACSL \
 -v ${_pwd}/OCaml:/home/opam/enum/OCaml \
 -v ${_pwd}/ptrWhy3:/home/opam/enum/ptrWhy3 \
 --name="enumctr" enum:latest


