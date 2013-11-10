#   To build (check the proofs and produce *.vo files):
#     make

#   To make the documentation (and put it into ./src/html/. ):
#     make html

#   To install (put the *.vo files in a central location):
#     make install

#   To do all of the above:
#     make everything

#   To make the file src/TAGS :
#     make TAGS

#   To remove most of the files made:
#     make clean

#   To remove all of the files made:
#     make distclean

all clean install html TAGS: src/Make-include.mk
	$(MAKE) -C src $@
everything: all html install
distclean: clean
	rm -f src/Make-include.mk src/Make-include.mk.bak
src/Make-include.mk: src/Make-include.in
	cd src && coq_makefile -f Make-include.in
