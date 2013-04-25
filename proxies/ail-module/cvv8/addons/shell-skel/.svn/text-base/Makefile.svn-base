#!/usr/bin/make -f
########################################################################
include ../../config.make # see that file for certain configuration options.
shell.BIN.OBJECTS := shell.o
shell.BIN.LDFLAGS += $(BINS_LDFLAGS) $(LDFLAGS_V8)
$(eval $(call ShakeNMake.CALL.RULES.BINS,shell))
all: $(shell.BIN)
