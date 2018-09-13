Copyright 2018 Alain Giorgetti and Rémi Lazarini
FEMTO-ST institute

This software is distributed under the terms of the GNU Lesser
General Public License version 2.1

The code in this archive is documented by the following papers (in French):

[GL18]    A. Giorgetti and R. Lazarini. Preuve de programmes d’énumération avec Why3.
          In AFADL’18, pages 14–19, 2018.
          http://afadl2018.ls2n.fr/wp-content/uploads/sites/38/2018/06/AFADL_Procs_2018.pdf.
          Local copy GL18afadl.pdf.

[GL18ext] A. Giorgetti and R. Lazarini. Preuve de programmes d’énumération avec Why3.
          Extended version of [GL18]. File GL18extended.pdf.

Developed by Alain Giorgetti and Rémi Lazarini in 2018.

1. CONTENTS
===========

The files GL18afadl.pdf [GL18] and GL18extended.pdf [GL18ext] (in French) are a 
published paper and its extended version with an interactive proof of completeness 
of the generator of permutations.

The files Permutation.mlw and Barray.mlw contain the generators of permutations
and bounded arrays presented in [GL18].

The file Permutation1.mlw contains more specifications to prove completeness of the generator
of permutations. This proof is described in [GL18ext].

The folders Barray, Permutation and Permutation1 contain the "why3 session" files.

The Dockerfile contains commands to build a Docker image to install all the tools (under 
Linux Ubuntu 16/04) and replay the proofs.

The file gui.sh is a bash script to create the Docker container.

2. COPYRIGHT
============

This work is distributed under the GNU LGPL 3. See the enclosed LICENSE file.

3. EXECUTION
============

The code is currently developed and maintained only for Linux. There are two methods to
experiment with it.

3.1. With installed tools
-------------------------

If you have already installed Why3, Alt-Ergo, CVC4, Z3 and Coq under Linux, you can try to replay
the proofs with Why3 ide, as follows:

1. Extract the archive
    zip gl18.zip -d gl18
2. Enter the folder
    cd gl18
3. Start Why3 ide with Permutation1.mlw
    make idepermut1
4. See other possible proving actions in Makefile

3.2. In a Docker container
--------------------------

If the former method fails, you can create a Docker container with compatible releases of all the
tools, as follows:

1. If Docker is not installed, follow the instructions at
    https://docs.docker.com/install/linux/docker-ce/ubuntu/
   to install Docker
2. Copy gl18.zip in your personal folder (~/)
3. Open a terminal in your personal folder
4. Extract the archive
    zip gl18.zip -d gl18
5. Enter the folder
    cd gl18
6. Build the Docker image
    make build
7. Create the Docker container
    bash gui.sh
8. Run the container, attached to the terminal
    make start (you are in the Docker container)
9. Apply steps 2-4 of method 3.1

This execution method have been successfully tested under Linux Ubuntu 16.04, with Docker 18.03.1-ce.
