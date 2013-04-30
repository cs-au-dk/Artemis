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
# - At least one of sqlite3 and/or MySQLv5 dev files (headers and
# libraries).
#
# - v8::convert: http://code.google.com/p/v8-juice/wiki/V8Convert
#   (it's a header-only library, so required to special installation).
#   This makefile assumes it lives at ../../include.
#
########################################################################
include ../../config.make # see that file for certain configuration options.

########################################################################
# If needed, append the CPPFLAGS to point to where <v8/convert/*.hpp> can
# be found.


########################################################################
# Try to find sqlite3... If we find the header, we assume the library
# is in some default location.
#
# FIXME: port in the whiki makefile code which allows us to drop in
# our own sqlite3.c (from the sqlite3 amalgamation build).
CPDO_ENABLE_SQLITE3 ?= $(shell whereis sqlite3.h | cut -d: -f2 | grep include/sqlite3.h >/dev/null && echo 1)
LDFLAGS_SQLITE3 ?= -lsqlite3

########################################################################
# Try to find mysql_config. If we find it we assume that the dev files
# are installed and that mysql_config can tell us how to link to
# mysql.
BIN_MYSQL5_CONFIG := $(call ShakeNMake.CALL.FIND_BIN,mysql_config)
ifneq (,$(BIN_MYSQL5_CONFIG))
    CPDO_ENABLE_MYSQL5 := 1
    LDFLAGS_MYSQL5 := $(shell $(BIN_MYSQL5_CONFIG) --libs)
    CFLAGS_MYSQL5 := $(shell $(BIN_MYSQL5_CONFIG) --cflags)
else
    CPDO_ENABLE_MYSQL5 ?= 0
    LDFLAGS_MYSQL5 ?=
endif

# Normalize the options to 1/0 values...
ifneq (1,$(CPDO_ENABLE_SQLITE3))
  CPDO_ENABLE_SQLITE3 := 0
endif
ifneq (1,$(CPDO_ENABLE_MYSQL5))
  CPDO_ENABLE_MYSQL5 := 0
endif

########################################################################
# The library is useless without at least one db driver, so we bail out
# if we didn't find one...
ifeq (00,$(CPDO_ENABLE_MYSQL5)$(CPDO_ENABLE_SQLITE3))
  $(error The configuration process found neither sqlite3 nor mysql5 dev files.)
endif


########################################################################
# The rest of the code "shouldn't" need to be hacked for most Unix
# systems.

########################################################################
# Build shared library and link it against the underlying db libs
# (so client binaries won't have to)...
BA.DIR := ../bytearray
$(BA.DIR)/bytearray.hpp $(BA.DIR)/bytearray.cpp:
bytearray.hpp: $(BA.DIR)/bytearray.hpp 
	cp $(BA.DIR)/$@ .
bytearray.cpp: $(BA.DIR)/bytearray.cpp bytearray.hpp
	cp $(BA.DIR)/$@ .
bytearray.o: bytearray.cpp
CLEAN_FILES += bytearray.cpp bytearray.hpp
LDFLAGS_DRIVERS :=
jspdo.o: bytearray.cpp# w/o this dep, bytearray.hpp is not being copied?
libjspdo.LIB.OBJECTS := cpdo_amalgamation.o jspdo.o bytearray.o
#libjspdo.DLL.LDFLAGS := $(LDFLAGS_V8)
ifeq (1,$(CPDO_ENABLE_SQLITE3))
    LDFLAGS_DRIVERS += $(LDFLAGS_SQLITE3)
    cpdo_amalgamation.o: CFLAGS+=$(CFLAGS_SQLITE3)
endif

ifeq (1,$(CPDO_ENABLE_MYSQL5))
    LDFLAGS_DRIVERS += $(LDFLAGS_MYSQL5)
    cpdo_amalgamation.o: CFLAGS+=$(CFLAGS_MYSQL5)

endif
libjspdo.DLL.LDFLAGS += $(LDFLAGS_DRIVERS)
libjspdo.DLL.LDFLAGS += -lz# for ByteArray

libjspdo.DLL.OBJECTS := $(libjspdo.LIB.OBJECTS)
libjspdo.DLL: $(libjspdo.LIB.OBJECTS)
$(eval $(call ShakeNMake.CALL.RULES.DLLS,libjspdo))
all: $(libjspdo.DLL)
ifeq (0,$(CPDO_ENABLE_MYSQL5))
  # MySQL cannot be linked to statically on Linux platforms (and
  # possibly others) because it uses network-level libraries which do
  # not support static linking. Or so g++ tells me.
  # v8 appears to have this same problem, but i can't imagine why
  # it uses getaddrinfo()
  $(eval $(call ShakeNMake.CALL.RULES.LIBS,libjspdo))
  all: $(libjspdo.LIB)
else
  $(info MySQL is enabled, so we are NOT building a static library.)
endif

OBJS_NEEDING_DB_CPPFLAGS := cpdo_amalgamation.o
# jspdo.o
$(OBJS_NEEDING_DB_CPPFLAGS): CPPFLAGS+=-DCPDO_ENABLE_SQLITE3=$(CPDO_ENABLE_SQLITE3)
$(OBJS_NEEDING_DB_CPPFLAGS): CPPFLAGS+=-DCPDO_ENABLE_MYSQL5=$(CPDO_ENABLE_MYSQL5)



EXT.JS := jspdo-init.js
EXT.CPP := jspdo-init.cpp
$(EXT.JS):
jspdo.o: $(EXT.CPP)

js2c: js2c.c Makefile
# adding $(MAKEFILE_LIST) as a dep causes a circular dep on .make.c_deps and js2c???
	$(CC) -o $@ js2c.c
CLEAN_FILES += js2c
$(EXT.CPP): js2c $(EXT.JS) $(ALL_MAKEFILES)
	./js2c jspdoInitCode < $(EXT.JS) > $@

########################################################################
# Binaries...
LDFLAGS_JSPDO := -L. -ljspdo #$(LDFLAGS_DRIVERS)
SHELL_LDFLAGS := $(LDFLAGS_JSPDO)
#ifeq (0,$(CPDO_ENABLE_MYSQL5))
#  SHELL_LDFLAGS += -static $(LDFLAGS_DRIVERS)
#endif
SHELL_BINDINGS_HEADER := jspdo.hpp
SHELL_BINDINGS_FUNC := cvv8::JSPDO::SetupBindings
SHELL_DEPS := $(libjspdo.DLL) $(libjspdo.LIB)
SHELL.NAME := jspdo
include ../shell-common.make

.PHONY: amal-cpp
amal-cpp: cpdo_amalgamation.o
	gcc -c -Iinclude cpdo_amalgamation.cpp \
		-Wall -Werror -pedantic -ansi \
		-DCPDO_ENABLE_SQLITE3=$(CPDO_ENABLE_SQLITE3) \
		-DCPDO_ENABLE_MYSQL5=$(CPDO_ENABLE_MYSQL5) \
		$(CFLAGS_MYSQL5)
