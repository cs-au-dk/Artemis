#!/bin/bash

# Process a sequence of *.gv files into images, resize them and then stitch into a movie file.

# Check for required software.
dot -V > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "Requires 'dot' from GraphViz."
    exit 1
fi

convert -version > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "Requires 'convert' from ImageMagick."
    exit 1
fi

avconv -version > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "Requires 'avconv' from libav."
    exit 1
fi

# Request the file pattern from the user.
echo "Enter the pattern for the files to convert: (e.g. my_image_*.gv)"
read img_pattern

shopt -s nullglob # Don't include literal * if there are no matches.
num_matches=`echo $img_pattern | wc -w` # Makes various assumptions about nothing weird (e.g. spaces!) being in the file names.
echo "Matched $num_matches files."

if [ $num_matches -lt 1 ]; then
    exit 1
fi

# Calculate a file name template.
name_template=${img_pattern/\*/%05d} # Replace (first) * by %05d.
name_template="${name_template%.gv}.png" # Replace .gv (if any) and add .png.
name_blank=`printf $name_template 0`

echo "Name template: $name_blank"

echo "Continue with these settings?"
select yn in "Yes" "No"; do
    case $yn in 
        Yes ) break ;;
        No ) exit 0 ;;
    esac
done


# Loop through the matching files, in sorted order, and generate the (renamed) image files.
count=1
img_files=()
echo -n "Generating images."
for gv_file in `ls -1 $img_pattern | sort -V`
do
    img_name=`printf $name_template $count`
    
    echo -en "\rGenerating $img_name from $gv_file.";
    
    dot -Tpng $gv_file -o $img_name
    
    img_files+=($img_name)
    
    let count++;
done
echo ""
#echo "Generated ${#img_files[@]} images."


# Loop through the image files and resize them to HD resolution 1920x1080.
echo -n "Resizing images."
for img_name in ${img_files[@]}
do
    echo -en "\rResizing $img_name"
    
    # See http://www.imagemagick.org/Usage/resize/ under "Resizing to Fill a Given Space"
    # avconv seems much happier with jpeg input than png.
    convert $img_name -resize 1920x1080 -size 1920x1080 xc:white +swap -gravity center -composite ${img_name%.png}.jpg
done
echo ""


# Set up the animation name.
name_template_2=${name_template/05d/s}
movie_name=`printf $name_template_2 animation`
movie_name="${movie_name%.png}.mp4"

name_template_3="${name_template%.png}.jpg"


# Choose the FPS.
framerate=""
while [[ ! $framerate =~ ^[0-9]+$ ]]; do
    echo "What frame rate would you like?"
    read framerate
done


# Stitch the images together into an animation.
# Options chosen by randomly selecting some found via google and any suggested by error messages.
avconv -r $framerate -f image2 -i $name_template_3 -vcodec mpeg4 -s 1920x1080 -vsync cfr -pix_fmt yuv420p $movie_name



