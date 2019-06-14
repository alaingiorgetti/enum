Copyright (C) 2014-2019 Clotilde Erard, Richard Genestier and Alain Giorgetti

ENUM in C/ACSL, verified with the WP plugin of the Frama-C platform.

Files and folders
=================

The folder 'fcts' contains auxiliary C functions. The folder 'fxtbook' 
contains effective generators implemented from the [fxtbook]. The  older 
'generation' contains other effective generators and generators obtained by 
filtering. The generators implemented in /fxtbook and generation/ are 
sequential generators composed of two generation functions first_..() and 
next_..().

How to use this code?
=====================

See the files Makefile in the folders 'fxtbook' and 'generation' for the different 
possible actions (compilation, test, etc). 
The 'wp' command allows you to replay the proofs with the WP plugin. 
Note that this command only works in a specific Docker container with Frama-C 
and the supported Why3 version. See the Makefile to build this container.