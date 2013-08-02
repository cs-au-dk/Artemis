#!/bin/bash

# Author : Prateek Saxena
# Copyright 2010 See LICENSE.txt
# See LICENSE.txt

# Modified for Artemis!

INPUT=/tmp/kaluza
OUTPUT=/tmp/kaluza-result

if [ -z "${ARTEMISDIR+xxx}" ]; 
then 
    # Default
    echo "Please set ARTEMISDIR env variable to the directory containing the Artemis INSTALL file"
    exit 1
fi;

KALUZABIN=$ARTEMISDIR/contrib/Kaluza/

YICESPATH="$KALUZABIN/yices-1.0.27/bin/yices"

if [ ! -e "$YICESPATH" ]; then
    echo "Yices 1.0.27 is not installed, and is required. You can simply download it from http://yices.csl.sri.com/download.shtml"
    echo "Please check that the yices binary exists at $YICESPATH, and then rerun."
    exit 1;
fi

CWD="$PWD";

cd $KALUZABIN;
rm -f corecstrs.tmp*;

export HAMPIPATH="$KALUZABIN/hampi";

if [ ! -e "$HAMPIPATH"/hampi.sh ];then
    echo "$HAMPIPATH/hampi.sh does not exist! dying ...";
    echo "Perhaps you need to run \"cd $HAMPIPATH ; ./configure ; make\"."
    exit 1;
fi

if ./ksolver < /tmp/kaluza ;then
    if ./solveselects.sh corecstrs.tmp > stdout 2>stderr ;then
        
        if [ ! -e 'corecstrs.tmp.length.ys.out' ];then
            echo 'Error, No output length file generated! Dying...'
            exit 1
        fi
        
        if [ ! -e 'corecstrs.tmp.final.stp.out' ];then
            echo 'Error, No final BV encoder solved output file generated! Dying...';
            exit 1
        fi

        if grep -q -i "Invalid." corecstrs.tmp.final.stp.out ; then
            echo "UNSAT."
            exit 1
        fi
        
        if ! grep -q -i "^sat$" corecstrs.tmp.length.ys.out ; then
            echo "UNSAT."
            exit 1
        fi
        
        cat corecstrs.tmp.length.ys.out | grep -vi 'COPY' | grep -vi "^sat$" | awk '{print $2, substr($3, 0, index($3, ")") - 1)}' > $OUTPUT # ignore lines containing COPY
        
        #./convert.pl < corecstrs.tmp.final.stp.out | grep -vi COPY >> $OUTPUT
        
        exit 0
    
    else 
        
        echo "Error, Solverselects.sh failed"
        exit 1
        
    fi 
    
else

    echo "Error parsing! Check stdout and stderr ..."
    exit 1
    
fi

echo "Error, end-of-script should not be reached..."
exit 1

