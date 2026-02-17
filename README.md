# PropositionalLogicProof
This project implements the soundness and completeness in propositional logic in Rocq. 

To compile PropositionalLogicProof, you will need [Coq](https://coq.inria.fr/). We recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.16**.


## Environment Setup
```
# initialize opam
opam init -a

# create a switch named propl and import the environment
opam switch create propl
opam switch import opam-switch.export

# check if the switch and packages are right
opam switch
opam list
```


## Compile & Running PropositionalLogicProof
1. Generate Makefile if it is the first time, run `coq_makefile -f _CoqProject -o Makefile`.

2. Compile, run `make` in the current directory.


## Directory Contents

* Main.v - entry to run the project 
* Syntax.v - syntax of the propositional formula
* Semantics.v - semantics, defined satisfaction of the formala and entailment
* ProofSystem.v - inductive proof rules
* Soundness.v - prove the soundness theory
* Completeness.v - prove the completeness theory

