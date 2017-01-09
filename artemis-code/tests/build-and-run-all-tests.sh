#!/bin/bash

# Does a full clean and build and runs all the tests we have.

# Usage:
# ./build-and-run-all-tests.sh [--skip-build]
# The --skip-build option just runs the tests with the currently built artemis/webkit.

# Exit codes
# 0 - Success (N.B. Includes if the tests fail!)
# 1 - Bad arguments
# 100 - Clean failed
# 101 - WebKit build failed
# 102 - Artemis build failed
# 103 - Unit test build failed (not used, we just skip the unit tests in this case.)

# The test files to be run in artemis-code/tests/system
# They are expected to use the python unittest output format.
SYSTEMTESTS=(tests.py concolic.py concolic_engine.py delegation.py solver.py symbolic.py visibility.py server.py)


# Save all summary lines output by this script so they can be appended at the end.
exec 3>&1 4>&2 > >(awk -W interactive 'BEGIN {summary[0]="";summary[1]="========================================";i=2} /^Summary/ {summary[i++]=$0; print; next} /^PRINT_SUMMARY$/ {for (idx = 0; idx < i; idx++) {print summary[idx]}; exit} /.*/ {print; next}' | tee "$ARTEMISDIR/test-log_$(date +'%F_%T').txt") 2>&1



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

# Check arguments
USAGE="Usage:\n./build-and-run-all-tests.sh [--skip-build]\nThe --skip-build option just runs the tests with the currently built artemis/webkit."
BUILD=1
if [[ $# -eq 1 ]];
then
    if [[ "$1" == "--skip-build" ]];
    then
        BUILD=0
    else
        echo -e $USAGE
        exit 1
    fi
elif [[ $# -gt 1 ]];
then
    echo -e $USAGE
    exit 1
fi

if [[ $BUILD -eq 1 ]];
then
    
    # Clean
    echo -n "Build.Clean "
    CLEAN_TIME="$(time ($((make all-clean && rm -r WebKit/WebKitBuild/*) >/dev/null 2>&1)) 2>&1 1>/dev/null )"
    
    if [[ $? -eq 0 ]];
    then
        echo "OK"
        echo "Summary.Build.Clean Cleaned in ${CLEAN_TIME}s. OK"
    else
        echo "FAIL"
        exit 100
    fi
    
    # Build WebKit
    echo -n "Build.WebKit "
    WEBKIT_TIME="$(time (make webkit-minimal-debug >/dev/null 2>&1) 2>&1 1>/dev/null )"
    
    if [[ $? -eq 0 ]];
    then
        echo "OK"
        echo "Summary.Build.WebKit WebKit built in ${WEBKIT_TIME}s. OK"
    else
        echo "FAIL"
        exit 101
    fi
    
    # Build Artemis
    echo -n "Build.Artemis "
    ARTEMIS_TIME="$(time (make -B artemis >/dev/null 2>&1) 2>&1 1>/dev/null )"
    
    if [[ $? -eq 0 ]];
    then
        echo "OK"
        echo "Summary.Build.Artemis Artemis built in ${ARTEMIS_TIME}s. OK"
    else
        echo "FAIL"
        exit 102
    fi
    
else
    echo "Build.Clean SKIP"
    echo "Build.WebKit SKIP"
    echo "Build.Artemis SKIP"
fi



# Build unit tests
echo -n "Build.UnitTests "
cd artemis-code/tests/unit >/dev/null 2>&1
UNITTEST_TIME="$(time ($((qmake && make) >/dev/null 2>&1)) 2>&1 1>/dev/null )"

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
    #exit 103
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
    
    ./"$TESTFILE" -v 2>&1 1>/dev/null | awk -W interactive -v scriptname="$TESTNAME" '/^test(.*)\.\.\./ { printf "%s.%s.%s ", scriptname, substr($2, 11, length($2)-11), $1; for(i=4;i<=NF;++i){ printf "%s ", toupper($i) }; print ""; next } /^Ran/ { printf "Summary.%s %s. ", scriptname, $0; getline; getline; print $0; exit }'
    
done


# Finished.


echo "PRINT_SUMMARY"

# Resore stdout/stderr (ends the redirection process).
exec 1>&3 2>&4 3>&- 4>&-
sleep 1
echo ""

