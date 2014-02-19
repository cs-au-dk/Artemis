#!/bin/sh

# Call the entrypoint_identifier.py script but ignoring the LD_LIBRARY_PATH environment variable.
# This avoids some problems with different WebKit versions.

env LD_LIBRARY_PATH="" python ${ARTEMISDIR}/artemis-code/scripts/entrypoint_identifier.py "$@"
