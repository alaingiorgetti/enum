###################################################################
# Copyright (C) 2019 Alain Giorgetti and Clotilde Erard           #
# FEMTO-ST institute                                              #
###################################################################

###################################################################
#  This software is distributed under the terms of the GNU Lesser #
#  General Public License version 2.1                             #
###################################################################

# File: OCaml/generator/endo/Makefile

.PHONY: compile test clean

compile: *.ml
	ocamlbuild -pkg zarith Main.native

test: compile
	./Main.native

clean:
	rm -rf Main.native _build