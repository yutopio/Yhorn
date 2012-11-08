#!/bin/bash

OCAMLLIB=/usr/lib/ocaml
Z3=~/z3

cd $Z3/ocaml
gcc -I../include -I$OCAMLLIB -c z3_stubs.c z3_theory_stubs.c
ocamlc -c z3.mli z3.ml
ocamlc -a -o z3.cma -custom z3.cmo z3_theory_stubs.o z3_stubs.o -cclib -lcamlidl -ccopt -L../lib
