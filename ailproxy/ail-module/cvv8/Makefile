#!/usr/bin/make -f
########################################################################
# Main makefile for v8-convert.
########################################################################
include config.make # see that file for certain configuration options.

TMPL_GENERATOR_COUNT := 10# max number of arguments generated template specializations can handle
TYPELIST_LENGTH := 15# max number of args for Signature<T(...)> typelist
INCDIR_DETAIL := $(TOP_INCDIR)/cvv8/detail
sig_gen_h := $(INCDIR_DETAIL)/signature_generated.hpp
invo_gen_h := $(INCDIR_DETAIL)/invocable_generated.hpp
conv_gen_h := $(INCDIR_DETAIL)/convert_generated.hpp
TMPL_GENERATOR := $(TOP_SRCDIR_REL)/createForwarders.sh
MAKEFILE_DEPS_LIST = $(filter-out $(ShakeNMake.CISH_DEPS_FILE),$(MAKEFILE_LIST))
ifeq (1,1)
##########################################################################3
# script-based Signature generator...
createSignatureTypeList.sh:
$(sig_gen_h): $(TMPL_GENERATOR) createSignatureTypeList.sh $(MAKEFILE_DEPS_LIST)
	@echo "Creating $@ for typelists taking up to $(TYPELIST_LENGTH) arguments and" \
		"function/method signatures taking 1 to $(TMPL_GENERATOR_COUNT) arguments..."; \
	{ \
		echo "/* AUTO-GENERATED CODE! EDIT AT YOUR OWN RISK! */"; \
		echo "#if !defined(DOXYGEN)"; \
		bash ./createSignatureTypeList.sh 0 $(TYPELIST_LENGTH); \
		i=1; while [ $$i -le $(TMPL_GENERATOR_COUNT) ]; do \
		bash $(TMPL_GENERATOR) $$i MethodSignature ConstMethodSignature  || exit $$?; \
		i=$$((i + 1)); \
		done; \
		echo "#endif // if !defined(DOXYGEN)"; \
	} > $@
else
##########################################################################3
# Boost.Preprocessor-based Signature generator...
GEN_H_DIR := include/cvv8/generator
SIG_GEN_BOOST := Signature.hpp
$(SIG_GEN_BOOST):
$(sig_gen_h): $(SIG_GEN_BOOST) $(TMPL_GENERATOR) $(MAKEFILE_DEPS_LIST)
	@echo "Creating $@ for typelists taking up to $(TYPELIST_LENGTH) arguments and" \
		"function/method signatures taking 1 to $(TMPL_GENERATOR_COUNT) arguments..."; \
	{ \
		echo "/* AUTO-GENERATED CODE! EDIT AT YOUR OWN RISK! */"; \
		echo "#if !defined(DOXYGEN)"; \
		cd "$(GEN_H_DIR)" >/dev/null || exit; \
		gcc -E -P -I. -DCVV8_PP_ITER_MAX=$(TYPELIST_LENGTH) $(SIG_GEN_BOOST); \
		cd - >/dev/null; \
		i=1; while [ $$i -le $(TMPL_GENERATOR_COUNT) ]; do \
			bash $(TMPL_GENERATOR) $$i MethodSignature ConstMethodSignature  || exit $$?; \
		i=$$((i + 1)); \
		done; \
		echo "#endif // if !defined(DOXYGEN)"; \
	} > $@
endif
gen: $(sig_gen_h)
all: $(sig_gen_h)
$(invo_gen_h): $(TMPL_GENERATOR) $(MAKEFILE_DEPS_LIST)
	@echo "Creating $@ for templates taking 1 to $(TMPL_GENERATOR_COUNT) arguments..."; \
	{ \
		echo "/* AUTO-GENERATED CODE! EDIT AT YOUR OWN RISK! */"; \
		echo "#if !defined(DOXYGEN)"; \
		i=1; while [ $$i -le $(TMPL_GENERATOR_COUNT) ]; do \
			bash $(TMPL_GENERATOR) $$i \
				FunctionForwarder \
				MethodForwarder \
				CallForwarder \
				CtorForwarder \
			|| exit $$?; \
			i=$$((i + 1)); \
		done; \
		echo "#endif // if !defined(DOXYGEN)"; \
	} > $@;
gen: $(invo_gen_h)
all: $(invo_gen_h)

.PHONY: show-message
show-message:
	@echo 'This library is header-only and requires no compiling' \
		'(just generation of some code).'; \
		echo "To build the example/demo code:"; \
		echo "    cd examples; make"

all: show-message
