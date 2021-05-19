Copyright (C) 2014-2019 Clotilde Erard, Richard Genestier and Alain Giorgetti

ENUM in C/ACSL, verified with the WP plugin of the Frama-C platform.

Files and folders
=================

The folder 'fcts' contains auxiliary C functions. The folder 'fxtbook' 
contains effective generators implemented from the [fxtbook]. The folder 
'generation' contains other effective generators and generators obtained by 
filtering. The generators implemented in /fxtbook and generation/ are 
sequential generators composed of two generation functions first_..() and 
next_..().

How to use this code?
=====================

See the file Makefile for the different possible actions (compilation, 
proof, etc). See also the file Makefile in each subfolder.

Warning
=======

In ENUM 1.3, the provided Dockerfile is no longer suitable to build a Docker
image with Frama-C to prove the C code. This issue may be addressed in a 
future release of ENUM. It is possible to compile the C code in the container
described in ../INSTALL.md.

