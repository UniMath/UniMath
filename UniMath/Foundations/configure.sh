#!/bin/sh

cat Make.ini >Make
cat .package/files >>Make
coq_makefile -f Make -o Makefile
