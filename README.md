A formalization of incidence projective geometry in Coq
=======================================================

Features
========
This repository describe a formalization of incidence projective geometry using Coq proof assistant. We study two different descriptions of incidence projective geometry : a synthetic, mathematics-oriented one and a more practical computation-oriented one, based on the combinatorial concept of rank.

Licence
========

The code is released under the terms of the LGPL version 3.0.

How to install
==============

To use this library, first you need to install Coq. This project also requires the Containers library to compile : https://github.com/coq-contribs/containers
We tested the development using Coq version 8.4pl6, 8.5pl3 and 8.6. The <=8.3 versions are not supported. 
Then download and unpack the files, it will create a ProjectiveGeometry directory.
In this directory, type ./configure.sh and make to compile the files, it will create some .vo files.

The compilation can take several hours with our large benchmark Coq files. For faster compilation, it is suggested that you do not compile:
- Dev/fano_plane_rk_pg23.v
- Dev/fano_space_pg32.v

Files
=====

The archive has 2 subdirectories:
Dev/ contains the code of:
- axiom systems of incidence projective geometry
- axiom systems of rank and matroid theory
- proof of equivalence between incidence projective geometry and rank theory
- proof of Desargues theorem using rank
- benchmark of finites models using incidence projective geometry and rank
- bijection between points and lines
- some tests on Desargues / Pappus / hexamys / moulton / homegeneous model
- tactics
- ...

Benchmark contains the tests performed in Coq and with the TPTP provers (http://www.cs.miami.edu/~tptp/)


Contributors
============

David Braun
Nicolas Magaud
Julien Narboux
