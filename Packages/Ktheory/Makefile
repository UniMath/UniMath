# -*- makefile-gmake -*-

#   To build (check the proofs and produce *.vo files):
#     make

#   To make the documentation (and put it into ./src/html/. ):
#     make html

#   To install (put the *.vo files in a central location):
#     make install

#   To do all of the above:
#     make everything

#   To make the file src/TAGS:
#     make TAGS

#   To get a count of source lines:
#     make lc

#   To remove most of the files made:
#     make clean

#   To remove all of the files made:
#     make distclean

all lc everything clean distclean install html TAGS: src/Make-include.mk; $(MAKE) -C src $@
src/Make-include.mk: src/Make-include.in; cd src && coq_makefile -f Make-include.in
