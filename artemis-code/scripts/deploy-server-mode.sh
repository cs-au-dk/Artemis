#!/bin/bash

# Deploys the server mode stuff to a new directory.

if [[ $# -ne 1 ]]; then
    echo "Usage:"
    echo 'cd $ARTEMISDIR'
    echo "./artemis-code/scripts/deploy-server-mode.sh /path/to/deploy/dir"
    exit 1
fi

TARGET_DIR=$1

if [[ ! -d "$TARGET_DIR" ]]; then
    echo "Target directory is not a directory."
    exit 1
fi

if [[ $(ls "$TARGET_DIR") ]]; then
    echo "Target directory is not empty."
    exit 1
fi

function copy_in_file {
    FILE=$1
    NAME=$2
    if [[ -e "$FILE" ]]; then
        cp -r "$FILE" "$TARGET_DIR/$NAME"
    else
        echo "Could not find $FILE"
        echo "Are you running from the Artemis directory root?"
        exit 1
    fi
}

#TODO: Assumes Artemis is fully built with server mode enabled and working.

# Copy all the files
copy_in_file ./artemis-code/dist/artemis artemis
copy_in_file ./docs/sections/server.rst server.rst
mkdir "$TARGET_DIR/tests"
copy_in_file ./artemis-code/tests/system/server.py tests/server.py
copy_in_file ./artemis-code/tests/system/fixtures/server tests/fixtures

COMMIT=$(git show --no-patch --format="%h - %s")
COMMIT_SHA=$(git rev-parse HEAD)
COMMIT_TITLE=$()
BRANCH=$(git symbolic-ref --short HEAD)

cd "$TARGET_DIR"

# Generate the docs HTML.
rst2html server.rst server.html
rm server.rst

# Patch the test suite to work.
# FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures')
sed -i "s/^FIXTURE_ROOT.*/FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures')/" "$TARGET_DIR/tests/server.py"

# ARTEMIS_EXEC = os.path.join(os.path.dirname(os.path.realpath(__file__)), '..', 'artemis')
sed -i "s/^ARTEMIS_EXEC.*/ARTEMIS_EXEC = os.path.join(os.path.dirname(os.path.realpath(__file__)), '..', 'artemis')/" "$TARGET_DIR/tests/server.py"

# Add info linking this deploy to the current git commit.
VERSION_FILE="version.txt"
echo "Branch: $BRANCH" >> "$VERSION_FILE"
echo "Commit: $COMMIT" >> "$VERSION_FILE"
echo "GitHub: https://github.com/cs-au-dk/Artemis/commit/$COMMIT_SHA" >> "$VERSION_FILE"

# Set SVN ignore.
svn propset svn:ignore --recursive .output . > /dev/null

echo "Done."
