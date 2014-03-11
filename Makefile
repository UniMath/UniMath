# -*- makefile-gmake -*-
include Makefile-coq.make
OTHERFLAGS += -indices-matter
Packages/Foundations/hlevel2/algebra1b.vo : OTHERFLAGS += -no-sharing
ifeq ($(VERBOSE),yes)
OTHERFLAGS += -verbose
endif
ifeq ($(NO_SHARING),yes)
OTHERFLAGS += -no-sharing
endif
# TIME = time
COQC = $(TIME) $(COQBIN)coqc
