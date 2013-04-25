########################################################################
# This file should be included by all other Makefiles in the project.
# It can be tweaked to enable or disable certain compile-time library
# features.
default: all
all:

########################################################################
# You can touch these:
########################################################################
ShakeNMake.QUIET := 0# set to 1 to enable "quiet mode"

########################################################################
# Set ENABLE_DEBUG to 1 to enable whefs debugging information.
DEBUG ?= 1
ENABLE_DEBUG ?= $(DEBUG)

GCC_CFLAGS := -pedantic -Wall -Werror -fPIC -ansi
# argh: -Wextra causes build errors b/c v8.h has lots of unused-but-named parameters
CFLAGS += $(GCC_CFLAGS)
CXXFLAGS += $(GCC_CFLAGS)

########################################################################
# v8-specific stuff...
#
# Set V8_PREFIX to the top-level install path of your v8 installation.
# If ENABLE_DEBUG is set to non-0 then libv8_g is used.
V8_PREFIX ?= $(HOME)
LDFLAGS_V8 ?= -lpthread -L$(V8_PREFIX)/lib
CPPFLAGS += -I$(V8_PREFIX)/include
ifeq (0,$(ENABLE_DEBUG))
    LDFLAGS_V8 += -lv8
else
    LDFLAGS_V8 += -lv8_g
endif


########################################################################
# Don't touch anything below this line unless you need to tweak it to
# build on your box:
CONFIG.MAKEFILE := $(word $(words $(MAKEFILE_LIST)),$(MAKEFILE_LIST))
$(CONFIG.MAKEFILE):
TOP_SRCDIR_REL := $(dir $(CONFIG.MAKEFILE))
TOP_SRCDIR_REL := $(patsubst %/,%,$(TOP_SRCDIR_REL))# horrible kludge
#TOP_SRCDIR := $(shell cd -P $(TOP_SRCDIR_REL) && pwd)
TOP_SRCDIR := $(realpath $(TOP_SRCDIR_REL))
#$(error TOP_SRCDIR_REL=$(TOP_SRCDIR_REL)   TOP_SRCDIR=$(TOP_SRCDIR))
TOP_INCDIR := $(TOP_SRCDIR_REL)/include
INCLUDES += -I. -I$(TOP_INCDIR)
CPPFLAGS += $(INCLUDES)

SRC_DIR ?= .#$(PWD)
ShakeNMake.CISH_SOURCES := \
	$(wildcard $(SRC_DIR)/*.cpp) \
	$(wildcard $(SRC_DIR)/*.c) \
	$(wildcard $(SRC_DIR)/parser/*.c) \
	$(wildcard *.cpp)

CFLAGS += -std=c89

########################################################################
# common.make contains config-independent make code.
include $(TOP_SRCDIR_REL)/common.make
ALL_MAKEFILES := $(PACKAGE.MAKEFILE) $(ShakeNMake.MAKEFILE) $(CONFIG.MAKEFILE)
$(ALL_MAKEFILES):


########################################################################
ifeq (1,$(ENABLE_DEBUG))
  CPPFLAGS += -UNDEBUG -DDEBUG=1
  CFLAGS += -g -O0
  CXXFLAGS += -g -O0
else
  CFLAGS += -O2
  CXXFLAGS += -O2
  CPPFLAGS += -UDEBUG -DNDEBUG=1
endif

CLEAN_FILES += $(wildcard *.o *~)
