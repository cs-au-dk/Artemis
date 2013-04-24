PLUGIN_NAME := ConvertDemo
PLUGIN_OBJECTS := plugin.o
PLUGINS_SRC_DIR := ../../extra-plugins/src
X := $(shell test -d $(PLUGINS_SRC_DIR); echo $$?;)
ifneq (0,$(X))
  $(error Edit this makefile and set PLUGINS_SRC_DIR to the /path/to/v8-juice/extra-plugins/src)
endif
include $(PLUGINS_SRC_DIR)/plugin_template.make

CPPFLAGS += -I$(PWD)/../include
