Copyright (C) 2014-2019 Clotilde Erard, Richard Genestier, Alain Giorgetti and Rémi Lazarini

ENUM is a library of structured array generators.

The version in C is formally specified in ACSL and automatically verified with 
the WP plugin of the Frama-C platform. The version in WhyML is verified with Why3.

Authors: Clotilde Erard, Richard Genestier, Alain Giorgetti and Rémi Lazarini

FEMTO-ST institute (UMR CNRS 6174)

Contact: alain.giorgetti AT femto-st.fr

Documentation
=============

The project is documented by README files and the references below.


Folders
=======

cACSL
-----

  C generators, specified in ACSL for verification with the WP plugin of 
  the Frama-C platform. Significant subset of ENUM 1.0 (downloadable at 
  http://members.femto-st.fr/alain-giorgetti/en). Documented in cACSL/README.md.

cWhy3
-----

  Files extracted from WhyML generators in the folder ptrWhy3. DO NOT MODIFY.

docs
----

  Documentation

OCaml
-----

  Files extracted from WhyML generators in the folder Why3. DO NOT MODIFY.

ptrWhy3
-------

  WhyML generators extractable in C. 
  The driver for extracting C arrays is kindly provided by R. Rieu-Helft.

Why3
----

  WhyML generators extractable in OCaml, but not in C. Extension of ENUM 1.1.

Project home
============

https://github.com/alaingiorgetti/enum

Copyright
=========

This program is distributed under the GNU LGPL 3. See the enclosed file LICENSE.

How to use this code?
=====================

See the file Makefile for the different possible actions (compilation, 
proof, etc). See also the files Makefile in subfolders.

References
==========

[fxtbook] J. Arndt. Matters Computational - Ideas, Algorithms, Source Code 
 Published electronically at http://www.jjj.de, 2010.

[GGP15a] R. Genestier, A. Giorgetti, and G. Petiot. Gagnez sur tous les 
tableaux. In Vingt-sixièmes Journées Francophones des Langages Applicatifs 
(JFLA'15), Le Val d'Ajol, France, January 2015. https://hal.inria.fr/hal-01099135.

[GGP15b] R. Genestier, A. Giorgetti, and G. Petiot. Sequential generation 
of structured arrays and its deductive verification. In Tests and Proofs (TAP'15), 
volume 9154 of LNCS, pages 109–128. Springer, Heidelberg, 2015.
http://dx.doi.org/10.1007/978-3-319-21215-9_7.

[Genestier16] R. Genestier. Vérification formelle de programmes de génération 
de données structurées. In Approches Formelles dans l'Assistance au
Développement Logiciel (AFADL'16), pages 67–71, 2016. 
http://events.femto-st.fr/sites/femto-st.fr.gdr-gpl-2016/files/content/AFADL-2016.pdf.

[GG16] R. Genestier, and A. Giorgetti. Spécification et vérification 
formelle d'opérations sur les permutations. In Approches Formelles dans 
l'Assistance au Développement Logiciel (AFADL'16), pages 72–78, 2016.
http://events.femto-st.fr/sites/femto-st.fr.gdr-gpl-2016/files/content/AFADL-2016.pdf.

[DGG16] C. Dubois, A. Giorgetti, and R. Genestier. Tests and proofs
for enumerative combinatorics.  In Tests and Proofs (TAP'16), volume 6792 of LNCS, 
pages 57–75. Springer, 2016. http://dx.doi.org/10.1007/978-3-319-41135-4_4.

[GL18] A. Giorgetti and R. Lazarini. Preuve de programmes d’énumération avec Why3.
In AFADL’18, pages 14–19, 2018.
http://afadl2018.ls2n.fr/wp-content/uploads/sites/38/2018/06/AFADL_Procs_2018.pdf.
File [GL18afadl.pdf](https://github.com/alaingiorgetti/enum/blob/master/docs/GL18afadl.pdf).

[GL18ext] A. Giorgetti and R. Lazarini. Preuve de programmes d’énumération avec Why3.
Extended version of [GL18].
File [GL18extended.pdf](https://github.com/alaingiorgetti/enum/blob/master/docs/GL18extended.pdf).
