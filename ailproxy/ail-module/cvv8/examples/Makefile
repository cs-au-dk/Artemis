#!/usr/bin/make -f
########################################################################
# Main makefile for v8-convert test/demo code.
########################################################################
TOP_DIR := ../
include $(TOP_DIR)/config.make # see that file for certain configuration options.

ConvertDemo.o: ConvertDemo.cpp
SHELL.DIR := $(TOP_DIR)/addons/shell-skel
demo.BIN.OBJECTS := demo.o ConvertDemo.o
demo.BIN.LDFLAGS := $(LDFLAGS_V8)
$(eval $(call ShakeNMake.EVAL.RULES.BIN,demo))
all: $(demo.BIN)
SHELL.OBJECTS := ConvertDemo.o
SHELL_BINDINGS_HEADER := ConvertDemo.hpp
SHELL_BINDINGS_FUNC := BoundNative::SetupBindings

# gcc 4.6 got REAL pedantic and breaks lots of code...
CPPFLAGS += -Wno-error=unused-but-set-variable

########################################################################
# shell app...
include ../addons/shell-common.make
