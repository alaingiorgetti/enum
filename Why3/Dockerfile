######################################################################
# Copyright 2018 Alain Giorgetti and Rémi Lazarini                   #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# GNU make 4.1 or later is assumed to be installed on the host system

# OCaml 4.02.3 + latest versions of the OPAM package manager for Linux Ubuntu 16.04
FROM ocaml/opam:ubuntu-16.04_ocaml-4.02.3

# Set the working directory
WORKDIR /home/opam/app

RUN sudo apt-get update
# wget and time
RUN sudo apt-get install -yq wget
RUN sudo apt-get install time

######################################################################
# Installation of coqide                                             #
######################################################################

# For Coq and coqide
RUN sudo apt-get install --fix-missing -qq -yy libgtksourceview2.0-dev
RUN . ~/.profile && opam install -y coqide

######################################################################
# Installation of Why3                                               #
######################################################################

# Required for Why3:
RUN sudo apt-get install menhir && sudo apt-get install libmenhir-ocaml-dev

# Why3 0.88.2 installed from sources
ADD why3-0.88.2.tar.gz /home/opam/app/

# RUN ls -al /home/opam/app/

# The folder why3-0.88.2 is owned by 1001

RUN sudo chown "opam":"opam" /home/opam/app/why3-0.88.2 -R && \
 sudo chmod g+rwx "/home/opam/app/why3-0.88.2" -R && \
 ls -al /home/opam/app

RUN . ~/.profile && cd /home/opam/app/why3-0.88.2 && ./configure && make && sudo make install

# Installation of Why3 API
#RUN cd /home/opam/app/why3-0.88.2 && make byte opt && sudo make install-lib

######################################################################
# Installation of provers Alt-Ergo 1.3, CVC4 1.5 and Z3 4.7.1,       #
# prover detection for Why3                                          #
######################################################################

# Required for Alt-Ergo:
RUN sudo apt-get install -y libocamlgraph-ocaml-dev libzarith-ocaml libzarith-ocaml-dev libcreal-ocaml-dev
RUN sudo apt-get install -qq -yy autoconf
RUN opam install camlzip
# Installation of Alt-Ergo 1.30 via opam
RUN opam install alt-ergo

# Installation of Z3 4.7.1 from source
RUN sudo wget https://github.com/Z3Prover/z3/archive/z3-4.7.1.tar.gz \
    && sudo tar xzvf z3-4.7.1.tar.gz \
    && cd z3-z3-4.7.1 && sudo python scripts/mk_make.py \
    && cd build && sudo make && sudo make install

# Required for CVC4
RUN sudo apt-get install -y libboost-all-dev libreadline-dev

# Installation of CVC4 1.5 from source
RUN sudo wget http://cvc4.cs.stanford.edu/downloads/builds/src/cvc4-1.5.tar.gz \
    && sudo tar xzvf cvc4-1.5.tar.gz \
    && cd cvc4-1.5 && sudo contrib/get-antlr-3.4 \
    && sudo ./configure --with-antlr-dir=/home/opam/app/cvc4-1.5/antlr-3.4 ANTLR=/home/opam/app/cvc4-1.5/antlr-3.4/bin/antlr3 \
    && sudo make \
    && sudo make install \
    && sudo ldconfig

# Finds SMT solvers and Coq for Why3
RUN . ~/.profile && why3 config --detect-provers

