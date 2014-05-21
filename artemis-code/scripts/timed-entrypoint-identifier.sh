#!/bin/sh

# Run the entrypoint identifier script with a 5 minute timeout.

timeout 300 ${ARTEMISDIR}/artemis-code/scripts/entrypoint_identifier.py "$@"

