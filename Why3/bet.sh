######################################################################
# Copyright 2019 Alain Giorgetti and Clotilde Erard                  #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

#!/bin/bash
#
# File: bet.sh. Shell script for bounded-exhaustive testing (BET) with Why3.
#
# This shell script is a prototype for a new command
#   why3 test ..
# with similar parameters.
#
# See an example of use in generator/endo/Makefile.
#
# TODO:
# 1. Find a better way to generate Main.ml than adapting OCaml/generator/endo/Main.ml.

# Parameters:
#   $1 is a list '-L path1 -L path2 ..' of paths to used theories
#   $2 is the name of the WhyML file containing the test function
#   $3 is the complete prefix (Module.function) of the OCaml file 
#      in which the test function in Why3 is extracted (example: Endo__EndoSound.test_b_endo)

mkdir OCaml 2> /dev/null
# echo "why3 extract --modular --recursive -D ocaml64 $1 -o ./OCaml $2"
why3 extract --modular --recursive -D ocaml64 $1 -o ./OCaml $2

# Adaptation of OCaml/generator/endo/Main.ml:
echo "WARNING: Works only with the Docker container generated with the provided Dockerfile"
cp /home/opam/enum/OCaml/generator/endo/Main.ml ./OCaml/
cd OCaml
cat Main.ml | sed -e "s/Endo__Main.main/$3/g" > Main.ml.tmp
mv Main.ml.tmp Main.ml
# more Main.ml
ocamlbuild -pkg zarith Main.native
./Main.native
rm -f *.cmi *.cmx *.o *.bak
cd ..
exit
