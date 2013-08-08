#!/bin/bash

SOLVER="./yices-1.0.27/bin/yices"
SOLVERFLAGS=" -e"
STPFLAGS="-a -c -d -p -w"
STPBIN=$KALUZABIN/stp

if [ -z "${TMPDIR+xxx}" ]; 
then 
    # Default
    TMPDIR="/tmp"
fi;

# Cleanup
rm "$1.length.failcases" 
touch "$1.length.failcases"
rm "$1.tempresult"
touch "$1.tempresult"
rm $TMPDIR/hampiBounds -f ;

ROUND=0;


# Just solve integer constraints with select conditions
while true
do
    # If there are no boolean variable for BrPredSolver to iterate over, stop after 1 iteration
    if [ $ROUND -gt 0 ]
    then 
	if ! grep -q "_true" "$1.selects"; then
	    echo "UNSAT."
	    break;
	fi
    fi

    ./BrPredSolver -file $1 > $TMPDIR/foo.stp
    perl -pi -e 's/(.*) = TRUE/$1/' $TMPDIR/foo.stp
    mv $TMPDIR/foo.stp "$1.stp"
    $STPBIN $STPFLAGS  "$1.stp" > "$1.stp.out"
    perl -pi -e 's/<=>/ = /' "$1.stp.out"

    sed -i 's/0x\([a-f0-9]\)/0hex\1/gi' "$1.stp.out"


    ROUND=$(( $ROUND+1 ));
    echo "Doing round $ROUND ...."
    if grep -q "Valid" "$1.stp.out"; then
	# Not sure why I had this condition in there... Valid should should just mean that there is no solution.
#	if grep -q "_true" "$1.stp.out"; then
	    echo "UNSAT."
	    break;
#	fi
    fi
    
    cat "$1.stp.out" | grep -E "_true"  | cut -d' ' -f2,5 > "$1.selects"
    
# Flatten the if-else structures
if ! ./IfElseFlattner -file "$1" -selfile "$1.selects" -outfile "$1.simplified"; then
    echo "ERROR: cutting short solve selects as the IfElseFlattner failed";
    exit;
fi

# Build a concat graph, map strings to positions in the bitvector
./Concatgraph -file "$1.simplified" -out "$1.simplified.tmp" -outpos "$1.simplified.tmp.pos" > "$1".concatgraph
ITERNUM=1;

COUNTERVAR=20 ;

# Solve for integer constraints and lengths of all strings.
while ! grep -q "Done" "$1.tempresult"
  do
  rm -f $TMPDIR/hampiBounds  
  echo "unsat" > "$1.length.ys.out"
  # Optimization: Loop trying increasing Length bounds upto 300
  BREAKONEMORE=0
  while grep -q '^unsat' "$1.length.ys.out"
    do
    ./LenSolver -file "$1.simplified.tmp" -posfile "$1.simplified.tmp.pos" -lenb "$COUNTERVAR" > $TMPDIR/foo.ys
    cat "$1.length.failcases" >> $TMPDIR/foo.ys
    echo "(check)" >> $TMPDIR/foo.ys
    mv $TMPDIR/foo.ys "$1.length.ys"
    $SOLVER $SOLVERFLAGS "$1.length.ys" > "$1.length.ys.out"
    COUNTERVAR=$(( $COUNTERVAR+30 ));
    if [ "$COUNTERVAR" -gt "300" ]
	then
	echo "Unsatisfiable in this round: No Length constraints satisfy"
	BREAKONEMORE=1
	break;
    fi
  done
  
  if [ $BREAKONEMORE -eq 1 ] ;
  then
      BREAKONEMORE=0
      break;
  fi
  
  cat "$1.length.ys.out" | grep -v -E "^(sat|unsat)$" | grep "len_slot"  | cut -d')' -f1 | cut -d' ' -f2-  > "$1.length.outys"
  cat "$1.length.ys.out" | grep -v -E "^(sat|unsat)$" | grep "slotstart"  | cut -d')' -f1 | cut -d' ' -f2- >> "$1.length.outys"
  cat "$1.length.ys.out" | grep -v -E "^(sat|unsat)$" | grep "slotend"  | cut -d')' -f1 | cut -d' ' -f2-   >> "$1.length.outys"
  cat "$1.length.outys" | ./t.pl > "$1.length.out"

  LFILE="$1.length.out"
  if [ ! -s $LFILE ] ; 
      then
      echo "Done" > "$1.tempresult"
      echo "Unsatisfiable in this round: No Length constraints satisfy, $1.length.out is empty"
  fi 
  ./BVEncoder -file "$1.simplified.tmp" -posfile "$1.simplified.tmp.pos" -lengths  "$1.length.out" > "$1.final.stp";
  RETVAL=$?
  if [ $RETVAL -eq 0 ]
  then 
      echo -e "QUERY(FALSE);\n" >> "$1.final.stp"
      echo -e "COUNTEREXAMPLE;\n" >> "$1.final.stp"
      perl -pi -e 's/(.*) = TRUE/$1/' "$1.final.stp"
      $STPBIN $STPFLAGS  "$1.final.stp" >  "$1.final.stp.out"
      perl -pi -e 's/<=>/ = /' "$1.final.stp.out"
      sed -i 's/0x\([a-f0-9]\)/0hex\1/gi' "$1.final.stp.out"
      if ! grep -q "Valid" "$1.final.stp.out"
      then
 	  echo "Done" > "$1.tempresult"
	  echo "SAT."
	  exit 0
      else
	  grep -v "^(sat|unsat)$" "$1.length.ys.out" |  grep -E "len_" | ./negateclause.pl > $TMPDIR/test
 	  cat $TMPDIR/test >> "$1.length.failcases" 
 	  if [ -e "$TMPDIR/hampiBounds" ];then
 		  cat $TMPDIR/hampiBounds >> "$1.length.failcases";
 	  fi
      fi
  elif [ $RETVAL -eq 2 ] 
  then 
      echo "ERROR: BVEncoder failed"
      exit 1;
  elif  [ $RETVAL -eq 9 ] 
  then 
      if [ $ITERNUM -eq 1 ]
      then
	  grep -v "^(sat|unsat)$" "$1.length.ys.out" |  grep -E "len_" | ./negateclause.pl > $TMPDIR/test
	  cat $TMPDIR/test >> "$1.length.failcases" 
	  if [ -e "$TMPDIR/hampiBounds" ];then
 	      cat $TMPDIR/hampiBounds >> "$1.length.failcases";
	  fi
      else
	  echo "ASSERT (FinalInput = \"\");" >> "$1.final.stp.out"
	  echo "SAT. ASSERT (FinalInput = \"\");"
	  exit 0;
      fi
  else
      grep -v "^(sat|unsat)$" "$1.length.ys.out" |  grep -E "len_" | ./negateclause.pl > $TMPDIR/test
      cat $TMPDIR/test >> "$1.length.failcases" 
      if [ -e "$TMPDIR/hampiBounds" ];then
 	  cat $TMPDIR/hampiBounds >> "$1.length.failcases";
      fi
  fi
  echo -e "\n\n ****** END OF ITER ********* \n\n" ;
  ITERNUM=$(( $ITERNUM + 1));
  if [ "$ITERNUM" -gt "50" ];then
      echo "Unsatisfiable in this round: Tried 50 iters... trying new round"
      break;
  fi
done;
done
