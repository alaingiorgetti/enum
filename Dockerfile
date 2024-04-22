######################################################################
#  Copyright (C) 2019-2024 Alain Giorgetti, Clotilde Erard and       #
#                                           Jérome Ricciardi         #
#  FEMTO-ST institute                                                #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Dockerfile to build a Docker image with all tools for Enum 1.4

######################################################################
# 1. Debian                                                          #
######################################################################

FROM debian:buster-20210311-slim

USER root

######################################################################
# 2. Prerequisites                                                   #
######################################################################

RUN apt-get update && \
  apt-get -y install sudo && \
  sudo apt-get -y install pkg-config=0.29-6 libgtksourceview2.0-dev=2.10.5-3 \
    python2.7 libgtk-3-dev=3.24.5-1 libgtksourceview-3.0-dev=3.24.9-2 \
    wget=1.20.1-1.1 opam=2.0.3-1+deb10u1 -V \
    libgmp-dev && \
  adduser --disabled-password --gecos '' opam && \
  usermod -aG sudo opam

######################################################################
# 3. Confirm the working directory                                   #
######################################################################

WORKDIR /home/opam

######################################################################
# 4. Installation of CVC3, CVC4, Z3 from sources                     #
######################################################################

RUN wget https://cs.nyu.edu/acsys/cvc3/releases/2.4.1/linux64/cvc3-2.4.1-optimized-static.tar.gz && \
  tar -xzf cvc3-2.4.1-optimized-static.tar.gz && \
  sudo cp -R /home/opam/cvc3-2.4.1-optimized-static/* /usr/local/ && \
  sudo apt-get -y install cvc4=1.6-2+b1 -V && \
  wget https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-16.04.zip && \
  unzip z3-4.7.1-x64-ubuntu-16.04.zip && \
  sudo cp z3-4.7.1-x64-ubuntu-16.04/bin/z3 /usr/local/bin/z3-4.7.1 && \
  wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip && \
  unzip z3-4.8.10-x64-ubuntu-18.04.zip && \
  sudo cp z3-4.8.10-x64-ubuntu-18.04/bin/z3 /usr/local/bin/z3-4.8.10

######################################################################
# 5. Installation of Alt-Ergo, Coq, coqide, Why3, qcheck with opam   #
######################################################################

USER opam

RUN opam init -y --disable-sandboxing && \
  opam install -y depext.transition && \
  opam depext conf-m4 && \
  opam install -y --unlock-base coq.8.12.2 coqide.8.12.2 && \
  opam install -y why3.1.4.0 why3-ide.1.4.0 why3-coq.1.4.0 && \
  opam install -y alt-ergo.2.4.1

USER root

RUN ln /home/opam/.opam/default/bin/a* /home/opam/.opam/default/bin/c* \
 /home/opam/.opam/default/bin/d* /home/opam/.opam/default/bin/g* \
 /home/opam/.opam/default/bin/l* /home/opam/.opam/default/bin/m* \
 /home/opam/.opam/default/bin/o* /home/opam/.opam/default/bin/s* \
 /home/opam/.opam/default/bin/v* /home/opam/.opam/default/bin/w* /bin/

USER opam

RUN why3 config detect
