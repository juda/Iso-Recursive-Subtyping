Revisiting Iso-Recursive Subtyping (Artifact)
-----

## Abstract
This bundle contains the Coq formulation associated with the paper "Revisiting Iso-Recursive Subtyping". 
This document explains how to run the Coq formulations. 

## Getting Started

We strongly recommend you to install Coq proof assistant by ```opam2```.

1. Install [Coq](https://coq.inria.fr/opam-using.html)(>=8.10). The latest version of Coq is 8.12. In Ubuntu-like system, you can install Coq by typing these commands in terminal.
	
		
		>> opam install opam-depext
		>> opam-depext coq
		>> sudo apt-get install m4
		>> opam pin add coq 8.12.0
		

2. Install [metalib](https://github.com/plclub/metalib). In terminal, type

		
		>> git clone https://github.com/plclub/metalib.git
		>> cd metalib/Metalib
		>> make
		>> make install
		
3. Now to compile our Coq proof where a ```makefile``` is provided. In command line, cd to the ```src``` directory and then build the whole project.
	
		
		>> cd path_to_src
		>> make clean
		>> make
		>> make html
		
## Guide

The repo contains three sub-folders:

- __OOPSLA__: This is the Coq proof for our OOPSLA'20 paper, the paper-to-proofs correspondence guide can be found at the paper.

- __Journal__: This is the Coq proof for the extension version, the paper-to-proofs correspondence guide can be found at the paper.

- __SASyLF__: This is the SASyLF proof of double unfolding rules provided by John T. Boyland. It uses SASyLf, a proof assistant that using HOAS (higher order abstract syntax) technique while our Coq proof uses locally nameless. 