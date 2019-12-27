# OUVerT
Ohio University Verification Toolsuite

# REQUIREMENTS

coq 8.9.0
mathcomp algebra 1.7.0
mathcomp fingroup 1.7.0
mathcomp ssreflect 1.7.0

# BUILD

To build OUVerT, clone it and do:

> make

> make install

The latter command installs the OUVerT files in your local `.opam` directory.

To use OUVerT files in another development, simply import them with OUVerT.filename, as in: 

> Require Import OUVerT.dyadic.

# ORGANIZATION

Following are the primary files in the development:

* [axioms.v](https://github.com/OUPL/OUVerT/blob/master/axioms.v): Axiomatizes Pinsker's and Gibb's inequalities
* [bigops.v](https://github.com/OUPL/OUVerT/blob/master/bigops.v): Computable Ssreflect-style bigops
* [chernoff.v](https://github.com/OUPL/OUVerT/blob/master/chernoff.v): Chernoff inequalities
* [dist.v](https://github.com/OUPL/OUVerT/blob/master/dist.v): Distributions over finite types
* [dyadic.v](https://github.com/OUPL/OUVerT/blob/master/dyadic.v): Dyadic rational numbers
* [expfacts.v](https://github.com/OUPL/OUVerT/blob/master/expfacts.v): Facts about `e^x`
* [learning.v](https://github.com/OUPL/OUVerT/blob/master/learning.v): Basic results in learning theory
* [listlemmas.v](https://github.com/OUPL/OUVerT/blob/master/listlemmas.v): Basic results on lists
* [maplemmas.v](https://github.com/OUPL/OUVerT/blob/master/maplemmas.v): Basic results on map
* [numerics.v](https://github.com/OUPL/OUVerT/blob/master/numerics.v): Lemmas relating `Q`, `R`, and dyadics `D`
* [strings.v](https://github.com/OUPL/OUVerT/blob/master/strings.v): `Showable` types
* [vector.v](https://github.com/OUPL/OUVerT/blob/master/vector.v): A sparse vector library
