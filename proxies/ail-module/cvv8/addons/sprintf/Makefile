#!/usr/bin/make -f
########################################################################
# Main makefile for jspdo.
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

libv8sprintf.LIB.OBJECTS := jssprintf.o
libv8sprintf.DLL.LDFLAGS += $(LDFLAGS_DRIVERS)
libv8sprintf.DLL.OBJECTS := $(libv8sprintf.LIB.OBJECTS)
libv8sprintf.DLL: $(libv8sprintf.LIB.OBJECTS)
$(eval $(call ShakeNMake.CALL.RULES.LIBS,libv8sprintf))
all: $(libv8sprintf.LIB)
$(eval $(call ShakeNMake.CALL.RULES.DLLS,libv8sprintf))
all: $(libv8sprintf.DLL)


########################################################################
# shell app...
SHELL_LDFLAGS += -L. -lv8sprintf
SHELL_BINDINGS_HEADER := jssprintf.hpp
SHELL_BINDINGS_FUNC := cvv8::SetupJSPrintf
include ../shell-common.make
