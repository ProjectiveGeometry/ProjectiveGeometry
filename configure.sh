#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" | grep -v SandBox | grep -v Finite >> Make
coq_makefile -f Make -o Makefile
