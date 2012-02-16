#!/do/not/make -f
########################################################################
# To be included by add-on app which want to build a basic shell
# from shell-skel/shell.cpp which includes the addon's bindings.
########################################################################
ifeq (,$(SHELL_BINDINGS_FUNC))
#$(error Define SHELL_BINDINGS_FUNC to a function _name_ before including this file.)
$(warning SHELL_BINDINGS_FUNC not defined.)
endif

ifeq (,$(SHELL_BINDINGS_HEADER))
#$(error Define SHELL_BINDINGS_HEADER to a header file containing the function defined in SHELL_BINDINGS_FUNC.)
$(warning SHELL_BINDINGS_HEADER not defined.)
endif

ifeq (,$(SHELL_LDFLAGS)$(SHELL.OBJECTS))
$(warning You have not set SHELL_LDFLAGS or SHELL.OBJECTS, which means we might not be linking the shell to the add-on code.)
endif

ifeq (1,1)
  SHELL.DIR ?= ../shell-skel
#  shell.cpp: $(SHELL.DIR)/shell.cpp
#	cp $< $@
  SHELL.NAME ?= shell
  SHELL.ORIG.CPP := $(SHELL.DIR)/shell.cpp
  SHELL.LOCAL.CPP := _shell-$(SHELL.NAME).cpp
  SHELL.LOCAL.O := $(subst .cpp,.o,$(SHELL.LOCAL.CPP))
  $(SHELL.ORIG.CPP):
  $(SHELL.LOCAL.CPP): $(SHELL.ORIG.CPP)
	cp $< $@
  $(SHELL.LOCAL.O): $(SHELL.LOCAL.CPP)
  $(SHELL.NAME).BIN.OBJECTS := $(SHELL.LOCAL.O) $(SHELL.OBJECTS)
  $(SHELL.NAME).BIN.LDFLAGS := $(LDFLAGS_V8) $(SHELL_LDFLAGS)
  $(eval $(call ShakeNMake.CALL.RULES.BINS,$(SHELL.NAME)))
ifneq (,$(SHELL_BINDINGS_FUNC))
  $(SHELL.LOCAL.O): CPPFLAGS+=-DSETUP_SHELL_BINDINGS=$(SHELL_BINDINGS_FUNC)
endif
ifneq (,$(SHELL_BINDINGS_HEADER))
  $(SHELL.LOCAL.O): CPPFLAGS+=-DINCLUDE_SHELL_BINDINGS='"$(SHELL_BINDINGS_HEADER)"'
endif
  $(SHELL.LOCAL.O): $(ALL_MAKEFILES)
  $($(SHELL.NAME).BIN): $(SHELL_DEPS)
  CLEAN_FILES += $(SHELL.LOCAL.CPP) $(SHELL.LOCAL.O) $($(SHELL.NAME).BIN)
  all: $($(SHELL.NAME).BIN)
endif
