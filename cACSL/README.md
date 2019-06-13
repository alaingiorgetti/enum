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

See the file Makefile for the different possible actions (compilation, 
proof, etc). See also the file Makefile in each subfolder.
