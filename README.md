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

To use this library, first you need to install Coq. This project also requires the Containers library to compile : https://github.com/coq-contribs/containers.
We tested the development using Coq version 8.4.dev, 8.5.dev and 8.6.dev. The <=8.3 versions are not supported. The library has not been tested on newer versions since the opam coq-containers package is limited to version 8.6.dev.
Then download and unpack the files, it will create a ProjectiveGeometry directory.
In this directory, type ./configure.sh and make to compile the files, it will create some .vo files.

The compilation can take several hours with our large benchmark Coq files. For faster compilation, it is suggested that you do not compile:
- Dev/fano_plane_rk_pg23.v
- Dev/fano_space_pg32.v
- Dev/fano_plane_generated_model_pg27.v
- Dev/fano_plane_generated_model_pg28.v


Branches
========

We are currently dividing the repository into 4 branches:

- amai2018 for work about proof equivalence presented in the journal Annals of Mathematics and Artificial Intelligence
- aisc2018 for work about finite models submitted to International Conference on Artificial Intelligence and Symbolic Computation
- thesis2019 for the work done throughout the thesis
- master for the last revision 

Files
=====

The archive has 4 subdirectories:

Dev/ contains the code of:
- axiom systems of incidence projective geometry
- axiom systems of rank and matroid theory
- proof of equivalence between incidence projective geometry and rank theory
- proof of Desargues theorem using rank
- benchmark of finites models using incidence projective geometry and rank
- bijection between points and lines
- some tests on Desargues / Pappus / hexamys / moulton / homegeneous model
- proofs automatically generated from a certificate
- tactics
- ...

Benchmark/ contains the tests performed in Coq and with the TPTP provers (http://www.cs.miami.edu/~tptp/)

Prog/ contains non-Coq programs allowing:
- finite model generation
- incidence proof generation

SandBox/ contains some ongoing projects or tests


Contributors
============

David Braun

Nicolas Magaud

Julien Narboux
