#!/bin/bash

# Takes as input a list of graphviz graphs
# Converts these to pngs
# Then merges all the pngs into a single "animation" in a pdf file.

# Usage:
# ./graphs2pdf.sh graph1.gv graph2.gv ...


outfile=tree-animation.pdf
PNGFILES=""

for gvfile in "$@"; do
    echo "Converting $gvfile"
    pngfile=${gvfile}.png
    PNGFILES+=" $pngfile "
    dot -Tpng $gvfile -o $pngfile
done

#echo "$PNGFILES"

echo "Generating $outfile"

convert $PNGFILES $outfile

rm $PNGFILES
