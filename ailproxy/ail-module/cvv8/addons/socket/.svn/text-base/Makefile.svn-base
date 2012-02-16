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
BA.DIR := ../bytearray
$(BA.DIR)/bytearray.hpp $(BA.DIR)/bytearray.cpp:
bytearray.hpp: $(BA.DIR)/bytearray.hpp 
	cp $(BA.DIR)/$@ .
bytearray.cpp: $(BA.DIR)/bytearray.cpp bytearray.hpp
	cp $(BA.DIR)/$@ .
bytearray.o: bytearray.cpp
CLEAN_FILES += bytearray.cpp bytearray.hpp
bytearray.o socket.o: bytearray.cpp
libv8socket.LIB.OBJECTS := socket.o bytearray.o
libv8socket.DLL.LDFLAGS += -lz# for ByteArray.gzip() and friends
libv8socket.DLL.OBJECTS := $(libv8socket.LIB.OBJECTS)
libv8socket.DLL: $(libv8socket.LIB.OBJECTS)
$(eval $(call ShakeNMake.CALL.RULES.LIBS,libv8socket))
all: $(libv8socket.LIB)
$(eval $(call ShakeNMake.CALL.RULES.DLLS,libv8socket))
all: $(libv8socket.DLL)


########################################################################
# shell app...
SHELL.NAME := shell-socket
SHELL_LDFLAGS := -L. -lv8socket
SHELL_BINDINGS_HEADER := socket.hpp
SHELL_BINDINGS_FUNC := cvv8::JSSocket::SetupBindings
include ../shell-common.make
