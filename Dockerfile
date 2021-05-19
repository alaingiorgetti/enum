######################################################################
#  Copyright (C) 2019-2021 Alain Giorgetti, Clotilde Erard and       #
#                                           Jérome Ricciardi         #
#  FEMTO-ST institute                                                #
######################################################################

######################################################################
#  This software is distributed under the terms of the GNU Lesser    #
#  General Public License version 2.1                                #
######################################################################

# Dockerfile to build a Docker image with all tools for Enum 1.3

######################################################################
# 1. Debian                                                          #
######################################################################

FROM debian:buster-20210311-slim

USER root

# create user

RUN adduser --disabled-password --gecos '' opam

RUN usermod -aG sudo opam

######################################################################
# 2. Prerequisites                                                   #
######################################################################

RUN apt-get update

RUN apt-get -y install sudo

RUN sudo apt-get -y install pkg-config=0.29-6 libgtksourceview2.0-dev=2.10.5-3 python2.7=2.7.16-2+deb10u1 libgmp-dev=2:6.1.2+dfsg-4 libexpat1-dev=2.2.6-2+deb10u1 libgtk-3-dev=3.24.5-1 libgtksourceview-3.0-dev=3.24.9-2 wget=1.20.1-1.1 opam=2.0.3-1+deb10u1 -V

USER opam

RUN opam init -y --disable-sandboxing

RUN opam install -y depext.transition

RUN opam depext conf-m4

USER root

######################################################################
# 3. Confirm the working directory                                   #
######################################################################

WORKDIR /home/opam

######################################################################
# 4. Installation of CVC3, CVC4, Alt-Ergo, Z3, Coq and coqide        #
######################################################################

RUN wget https://cs.nyu.edu/acsys/cvc3/releases/2.4.1/linux64/cvc3-2.4.1-optimized-static.tar.gz \
 && tar -xzf cvc3-2.4.1-optimized-static.tar.gz \
 && sudo cp -R /home/opam/cvc3-2.4.1-optimized-static/* /usr/local/

RUN sudo apt-get -y install cvc4=1.6-2+b1 -V

RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-ubuntu-16.04.zip \
 && unzip z3-4.7.1-x64-ubuntu-16.04.zip \
 && sudo cp z3-4.7.1-x64-ubuntu-16.04/bin/z3 /usr/local/bin/z3-4.7.1

RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.10/z3-4.8.10-x64-ubuntu-18.04.zip \
 && unzip z3-4.8.10-x64-ubuntu-18.04.zip \
 && sudo cp z3-4.8.10-x64-ubuntu-18.04/bin/z3 /usr/local/bin/z3-4.8.10

USER opam

RUN opam install -y alt-ergo.2.4.0

RUN opam install -y --unlock-base coq.8.12.2 coqide.8.12.2

#####################################################################
# 5. Installation of Why3 and Why3-ide                              #
#####################################################################

RUN opam install -y why3.1.4.0 why3-ide.1.4.0 why3-coq.1.4.0

#####################################################################
# 6. Installation of QCheck                                         #
#####################################################################

RUN opam install -y ocamlbuild.0.14.0 qcheck.0.17

USER root

RUN ln /home/opam/.opam/default/bin/a* /home/opam/.opam/default/bin/c* \
 /home/opam/.opam/default/bin/d* /home/opam/.opam/default/bin/g* \
 /home/opam/.opam/default/bin/l* /home/opam/.opam/default/bin/m* \
 /home/opam/.opam/default/bin/o* /home/opam/.opam/default/bin/s* \
 /home/opam/.opam/default/bin/v* /home/opam/.opam/default/bin/w* /bin/

USER opam

RUN why3 config detect


#####################################################################
# 7. Text editor                                                    #
#####################################################################

USER root

RUN apt-get -y install vim

#####################################################################
# 8. Installation files removal                                     #
#####################################################################

RUN rm -rf cvc* z* *.tar.gz

USER opam
