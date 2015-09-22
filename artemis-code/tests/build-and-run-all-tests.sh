#!/bin/bash

# Does a full clean and build and runs all the tests we have.

# Exit codes
# 0 - Success (N.B. Includes if the tests fail!)
# 100 - WebKit build failed
# 101 - Artemis build failed
# 102 - Unit test build failed (not used, we just skip the unit tests in this case.)

# The test files to be run in artemis-code/tests/system
# They are expected to use the python unittest output format.
SYSTEMTESTS=(tests.py concolic.py delegation.py solver.py symbolic.py visibility.py server.py)


cd "$ARTEMISDIR"

# Print some header info
if [[ true ]];
then
    git diff-index --quiet HEAD --
    if [[ $? -eq 0 ]];
    then
        DIRTY=""
    else
        DIRTY="(dirty) "
    fi
    
    COMMIT=$(git show --no-patch --format="%h $DIRTY- %s")
    BRANCH=$(git symbolic-ref --short HEAD)
    
    echo "Artemis Test Suite"
    echo "Started: $(date +'%F %T')"
    echo "Branch: $BRANCH"
    echo "Commit: $COMMIT"
    echo "========================================"
    echo
fi


TIMEFORMAT="%R"

# Build WebKit
echo -n "Build.WebKit "
CLEAN_TIME="$(time ((make all-clean && rm -r WebKit/WebKitBuild/*) >/dev/null 2>&1) 2>&1 1>/dev/null )"
WEBKIT_TIME="$(time (make webkit-minimal-debug >/dev/null 2>&1) 2>&1 1>/dev/null )"

if [[ $? -eq 0 ]];
then
    echo "OK"
    echo "Summary.Build.Clean OK, Took ${CLEAN_TIME}s"
    echo "Summary.Build.WebKit OK, Took ${WEBKIT_TIME}s"
else
    echo "FAIL"
    exit 100
fi

# Build Artemis
echo -n "Build.Artemis "
ARTEMIS_TIME="$(time (make -B artemis >/dev/null 2>&1) 2>&1 1>/dev/null )"

if [[ $? -eq 0 ]];
then
    echo "OK"
    echo "Summary.Build.Artemis OK, Took ${ARTEMIS_TIME}s"
else
    echo "FAIL"
    exit 101
fi

# Build unit tests
echo -n "Build.UnitTests "
cd artemis-code/tests/unit >/dev/null 2>&1
UNITTEST_TIME="$(time ((qmake && make) >/dev/null 2>&1) 2>&1 1>/dev/null )"

if [[ $? -eq 0 ]];
then
    echo "OK"
    echo "Summary.Build.UnitTests OK, took ${UNITTEST_TIME}s"
    
    # Run unit tests
    # Prints only the test results
    #./dist/unit | awk '/ms\)$/ {print "UnitTests." $4 " " $2}'
    # Also prints a summary
    ./dist/unit | awk -W interactive '/ms\)$/ {print "UnitTests." $4 " " $2; next} /\[----------\].*total\)/ { printf "Summary.UnitTests.%s", $5; $1=""; print $0; next} /\[==========\] (.*) total\)/ {$1=""; printf "Summary.UnitTests%s [", $0; while(getline != 0){ printf "%s %s;", $4, $2 }; print "]"; exit }'
    
else
    echo "FAIL"
    #exit 102
fi


# Run system tests
cd ../system
for TESTFILE in ${SYSTEMTESTS[@]};
do
    TESTNAME=$(basename "$TESTFILE" .py)
    
    if [[ ! -f "$TESTFILE" ]];
    then
        echo "Summary.$TESTNAME Does not exist."
        continue
    fi
    
    if [[ ! -x "$TESTFILE" ]];
    then
        echo "Summary.$TESTNAME Not executable."
        continue
    fi
    
    ./"$TESTFILE" -v 2>&1 | awk -W interactive -v scriptname="$TESTNAME" '/^test/ { printf "%s.%s.%s ", scriptname, substr($2, 11, length($2)-11), $1; for(i=4;i<=NF;++i){ printf "%s ", toupper($i) }; print ""; next } /^Ran/ { printf "Summary.%s %s. ", scriptname, $0; getline; getline; print $0; exit }'
    
done


# Finished

