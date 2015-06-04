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

# Build if necessary
read -n 1 -p "Rebuild WebKit and Artemis? [y/N]: "; echo
if [[ $REPLY =~ ^[yY]$ ]]; then
    # Paranoid clean and build
    time (make all-clean && rm -r WebKit/WebKitBuild/* && make webkit-minimal-debug && make -B artemis)
    
    if [[ $? -ne 0 ]]; then
        echo "Build failied, aborting deploy."
        exit 1
    fi
fi

# Copy all the files
function copy_in_file {
    FILE=$1
    NAME=$2
    if [[ -e "$FILE" ]]; then
        cp -rL "$FILE" "$TARGET_DIR/$NAME"
    else
        echo "Could not find $FILE"
        echo "Are you running from the Artemis directory root?"
        exit 1
    fi
}

copy_in_file ./artemis-code/dist/artemis artemis
copy_in_file ./docs/sections/server.rst server.rst

mkdir "$TARGET_DIR/tests"
copy_in_file ./artemis-code/tests/system/server.py tests/server.py
copy_in_file ./artemis-code/tests/system/fixtures/server tests/fixtures

mkdir "$TARGET_DIR/lib"
copy_in_file ./WebKit/WebKitBuild/Release/lib/libQtWebKit.so.4 lib/libQtWebKit.so.4
copy_in_file /usr/local/lib/libqhttpserver.so.0.1.0 lib/libqhttpserver.so.0.1.0
copy_in_file /usr/lib/x86_64-linux-gnu/libqjson.so.0.8.1 lib/libqjson.so.0.8.1 # This can be installed via apt-get, but some systems have an older version which does not work.

# Fetch git info while still in the Artemis dir.
COMMIT=$(git show --no-patch --format="%h - %s")
COMMIT_SHA=$(git rev-parse HEAD)
BRANCH=$(git symbolic-ref --short HEAD)
git diff-index --quiet HEAD --
GIT_CHANGES=$?

cd "$TARGET_DIR"

# Generate the docs HTML.
rst2html server.rst server.html
rm server.rst

# Patch the test suite to work.
# FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures')
sed -i "s/^FIXTURE_ROOT.*/FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures')/" "$TARGET_DIR/tests/server.py"

# ARTEMIS_EXEC = os.path.join(os.path.dirname(os.path.realpath(__file__)), '..', 'run-artemis.sh')
sed -i "s/^ARTEMIS_EXEC.*/ARTEMIS_EXEC = os.path.join(os.path.dirname(os.path.realpath(__file__)), '..', 'run-artemis.sh')/" "$TARGET_DIR/tests/server.py"

# Add info linking this deploy to the current git commit.
VERSION_FILE="version.txt"
echo "Deployed:" $(date +'%F %T') >> "$VERSION_FILE"
echo "Branch: $BRANCH" >> "$VERSION_FILE"
    echo "Commit: $COMMIT" >> "$VERSION_FILE"
if [[ $GIT_CHANGES -ne 0 ]]; then
    echo "        [With changes]" >> "$VERSION_FILE"
fi
echo "GitHub: https://github.com/cs-au-dk/Artemis/commit/$COMMIT_SHA" >> "$VERSION_FILE"

# Add another version file for WebKit, which may not be deployed as often.
WEBKIT_VERSION_FILE="webkit-version.txt"
cp "$VERSION_FILE" "lib/$WEBKIT_VERSION_FILE"

# Set SVN ignore.
svn propset svn:ignore --recursive .output . > /dev/null

# Add wrapper script.
WRAPPER_FILE=run-artemis.sh
cat << 'EOF' > "$WRAPPER_FILE"
#!/bin/bash

# Runs artemis with the needed libraries.
# If run with no arguemnts, the server mode will run with default settings.
# If arguments are supplied, they will be passed directly to artemis itself instead of the defaults.

# Check the webkit lib is in place.

if [[ ! -f "$(dirname $0)/lib/libQtWebKit.so.4" ]]; then
    echo "WebKit library was not found at $(dirname $0)/lib/libQtWebKit.so.4"
    echo "Try running download-webkit.sh first?"
    exit 1
fi

# Runs the artemis server with the correct WebKit lib linked in and appropriate arguments.

export LD_PRELOAD="$(dirname $0)/lib/libQtWebKit.so.4 $(dirname $0)/lib/libqhttpserver.so.0.1.0 $(dirname $0)/lib/libqjson.so.0.8.1"

if [ $# -eq 0 ]; then
    exec $(dirname $0)/artemis --major-mode server --analysis-server-port 5500 -v all
else
    exec $(dirname $0)/artemis "$@"
fi

EOF
chmod +x "$WRAPPER_FILE"

# Upload webkit to webspace instead of leaving it here, as the file is too big to check in to svn.
if true; then
    read -n 1 -p "Re-upload WebKit library? [y/N]: "; echo
    if [[ $REPLY =~ ^[yY]$ ]]; then
        tar -czf artemis-webkit.tgz lib/libQtWebKit.so.4 "lib/$WEBKIT_VERSION_FILE"
        
        scp artemis-webkit.tgz bspence@linux.cs.ox.ac.uk:/fs/website/people/ben.spencer/
    fi
    
    #rm -f artemis-webkit.tgz lib/libQtWebKit.so.4
    
    # Do not re-add the lib in svn.
    svn add --force lib
    svn propset svn:ignore "libQtWebKit.so.4
$WEBKIT_VERSION_FILE" lib > /dev/null
    
    # Add a script to download the webkit lib.
    DOWNLOAD_FILE=download-webkit.sh
    cat << 'EOF' > "$DOWNLOAD_FILE"
#!/bin/bash

# Download the Artemis modified WebKit library.

cd "$(dirname $0)"
wget http://www.cs.ox.ac.uk/people/ben.spencer/artemis-webkit.tgz
tar -xzf artemis-webkit.tgz
rm artemis-webkit.tgz

EOF
    chmod +x "$DOWNLOAD_FILE"
    
fi


echo "Done."
