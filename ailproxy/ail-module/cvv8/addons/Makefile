#!/usr/bin/make -f
default: all


SUBDIRS := bytearray jspdo shell-skel socket sprintf time glob

.PHONY: $(SUBDIRS)
$(SUBDIRS):
	$(MAKE) -C $@

clean-%:
		$(MAKE) -C $* clean

all: $(SUBDIRS)

clean: $(patsubst %,clean-%,$(SUBDIRS))
