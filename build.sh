#!/bin/bash
cd src
ocamlbuild lmoch.native -pkg Z3
make
