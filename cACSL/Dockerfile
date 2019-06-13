######################################################################
# Copyright (C) 2019 Clotilde Erard and Alain Giorgetti              #
# FEMTO-ST institute                                                 #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Dockerfile to build a Docker image with Frama-C.

# 1. OCaml 4.07.0 and latest version of the OPAM package manager for Linux Ubuntu 18.04
FROM ocaml/opam2:ubuntu-18.04

# 2. Confirm the working directory
WORKDIR /home/opam

# 3.
RUN sudo apt-get update \
 && sudo apt-get install -y autoconf automake wget m4 time libgmp-dev \
 && sudo apt-get install -qq -yy debianutils graphviz libexpat1-dev libgnomecanvas2-dev \
 && sudo apt-get install -qq -yy libgtk2.0-dev libgtksourceview2.0-dev perl pkg-config zlib1g-dev

# 4. Frama-C with opam
RUN . ~/.profile \
 && opam update \
 && opam install depext -y \
 && opam depext --install -y frama-c

# 5. Why3 0.88.3 with opam
RUN . ~/.profile \
 && opam pin add why3 0.88.3 -n \
 && opam install why3 --unlock-base

# 6. Alt-Ergo 2.0.0 with opam
RUN . ~/.profile \
 && opam pin add alt-ergo 2.0.0 -n \
 && opam depext --install alt-ergo

######################################################################
# Installation of CVC3, CVC4 and Z3 from source                      #
######################################################################

# 7. CVC3 2.4.1
RUN wget http://www.cs.nyu.edu/acsys/cvc3/releases/2.4.1/linux64/cvc3-2.4.1-optimized-static.tar.gz \
 && tar -xzf cvc3-2.4.1-optimized-static.tar.gz \
 && sudo cp -R /home/opam/cvc3-2.4.1-optimized-static/* /usr/local/

# 8. CVC4 1.4
RUN wget http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.4-x86_64-linux-opt \
 && sudo cp cvc4-1.4-x86_64-linux-opt /usr/local/bin/cvc4 \
 && sudo chmod +x /usr/local/bin/cvc4

# 9. Z3 4.6.0
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.6.0/z3-4.6.0-x64-ubuntu-16.04.zip \
 && unzip z3-4.6.0-x64-ubuntu-16.04.zip \
 && sudo cp z3-4.6.0-x64-ubuntu-16.04/bin/z3 /usr/local/bin \
 && sudo chmod +x /usr/local/bin/z3

# 10. Remove the installation files
RUN rm -rf cvc* z*

# 11. Why3 detect provers and plugins
RUN . ~/.profile \
 && why3 config --detect-provers --detect-plugins
