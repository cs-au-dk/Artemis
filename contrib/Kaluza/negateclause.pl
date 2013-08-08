#!/usr/bin/perl

use warnings;
use strict;

my $final = "true";
while(<STDIN>) {
    chomp;
    if(m/(.*)/) {
	$final = sprintf("(and %s %s)", $final, $1); 
    }
}
if ($final eq "true") {
} else {
    print ("(assert (not", $final, "))");
}
