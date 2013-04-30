#!/usr/bin/make -f
########################################################################
#
########################################################################
include ../../config.make # see that file for certain configuration options.

libv8time.LIB.OBJECTS := time.o
libv8time.DLL.LDFLAGS += $(LDFLAGS_DRIVERS)
libv8time.DLL.OBJECTS := $(libv8time.LIB.OBJECTS)
libv8time.DLL: $(libv8time.LIB.OBJECTS)
$(eval $(call ShakeNMake.CALL.RULES.LIBS,libv8time))
all: $(libv8time.LIB)
$(eval $(call ShakeNMake.CALL.RULES.DLLS,libv8time))
all: $(libv8time.DLL)



########################################################################
# shell app...
SHELL_LDFLAGS := $(LDFLAGS_V8) -L. -lv8time
SHELL_BINDINGS_HEADER := time.hpp
SHELL_BINDINGS_FUNC := cvv8::time::SetupBindings
include ../shell-common.make
