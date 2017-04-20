#!/bin/sh

# Run CVC4 with a 1 minute timeout.

timeout 60 ${ARTEMISDIR}/contrib/CVC4/cvc4-2017-04-18-x86_64-linux-opt --strings-exp  --lang=smtlib2 --rewrite-divk "$@"

