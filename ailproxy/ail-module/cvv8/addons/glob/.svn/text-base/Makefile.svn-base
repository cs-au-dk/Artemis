#!/usr/bin/make -f
########################################################################
# Main makefile for v8::convert ByteArray code.
#
# Requires GNU Make 3.81+
#
# This file is pre-configured for compling directly from the
# v8::convert source tree in my own personal dev environments. See the
# comments in the various sections below for what might need to be
# tweaked (not too much, at least for Linux boxes).
#
# Requirements:
#
# - Google v8 headers + libs.
#
# - v8::convert: http://code.google.com/p/v8-juice/wiki/V8Convert
#   (it's a header-only library, so required to special installation)
#
########################################################################
include ../../config.make # see that file for certain configuration options.

########################################################################
# If needed, append the CPPFLAGS to point to where <v8/convert/*.hpp> can
# be found.

THE_OBJS := jsglob.o whglob.o
libv8glob.LIB.OBJECTS := $(THE_OBJS)
libv8glob.DLL.OBJECTS := $(libv8glob.LIB.OBJECTS)
libv8glob.DLL: $(libv8glob.LIB.OBJECTS)
$(eval $(call ShakeNMake.CALL.RULES.LIBS,libv8glob))
all: $(libv8glob.LIB)
$(eval $(call ShakeNMake.CALL.RULES.DLLS,libv8glob))
all: $(libv8glob.DLL)



########################################################################
# shell app...
shell: $(THE_OBJS)
SHELL_LDFLAGS := $(LDFLAGS_V8) $(THE_OBJS)
SHELL_BINDINGS_HEADER := jsglob.hpp
SHELL_BINDINGS_FUNC := cvv8::SetupGlobBindings
include ../shell-common.make
