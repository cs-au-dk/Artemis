#!/usr/bin/make -f
include ../config.make


OUT_PREFIX := libv8-convert-API-
clean-doxy:
	-rm -fr $(OUT_PREFIX)*

clean: clean-doxy

doc doxy:
	@echo "Generating API docs..."
	@doxygen
	@echo "Output is in: "; ls -1td $(OUT_PREFIX)*

all:
	@echo "Run 'make doc' to generate the API docs with doxygen."
