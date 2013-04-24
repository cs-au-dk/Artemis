#!/usr/bin/make -f
########################################################################

########################################################################
include ../../config.make # see that file for certain configuration options.

########################################################################
# If needed, append the CPPFLAGS to point to where <v8/convert/*.hpp> can
# be found.

CPPFLAGS += -DLIBREADLINECPP_USE_LIBREADLINE=1
libv8readline.LIB.OBJECTS := v8-readline.o Readline.o
libv8readline.DLL.LDFLAGS += -lreadline
libv8readline.DLL.OBJECTS := $(libv8readline.LIB.OBJECTS)
libv8readline.DLL: $(libv8readline.LIB.OBJECTS)
$(eval $(call ShakeNMake.CALL.RULES.LIBS,libv8readline))
all: $(libv8readline.LIB)
$(eval $(call ShakeNMake.CALL.RULES.DLLS,libv8readline))
all: $(libv8readline.DLL)



########################################################################
# shell app...
SHELL_LDFLAGS := -L. -lv8readline
SHELL_BINDINGS_HEADER := v8-readline.hpp
SHELL_BINDINGS_FUNC := cvv8::Readline::SetupBindings
include ../shell-common.make
