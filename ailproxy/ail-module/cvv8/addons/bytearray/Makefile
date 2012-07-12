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

ENABLE_ZLIB ?= 1
ifeq (,$(ENABLE_ZLIB))
  ENABLE_ZLIB := 0
endif
bytearray.o: CPPFLAGS+=-DByteArray_CONFIG_ENABLE_ZLIB=$(ENABLE_ZLIB)
libv8bytearray.LIB.OBJECTS := bytearray.o
libv8bytearray.DLL.OBJECTS := $(libv8bytearray.LIB.OBJECTS)
libv8bytearray.DLL: $(libv8bytearray.LIB.OBJECTS)
ifeq (1,$(ENABLE_ZLIB))
  libv8bytearray.DLL.LDFLAGS += -lz
endif
$(eval $(call ShakeNMake.CALL.RULES.LIBS,libv8bytearray))
all: $(libv8bytearray.LIB)
$(eval $(call ShakeNMake.CALL.RULES.DLLS,libv8bytearray))
all: $(libv8bytearray.DLL)



########################################################################
# shell app...
SHELL_LDFLAGS := $(LDFLAGS_V8) -L. -lv8bytearray
SHELL_BINDINGS_HEADER := bytearray.hpp
SHELL_BINDINGS_FUNC := cvv8::JSByteArray::SetupBindings
include ../shell-common.make
