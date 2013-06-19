#!/usr/bin/perl -w 
use strict;

# Author : Devdatta Akhawe
# Copyright 2010
# See LICENSE.txt for details

while(<>){
	chomp;
	my $line=$_;
	
	if( $line =~ m/.*0hex([a-fA-F0-9]*).*/){
	my $t = $1 ;
	my $str = $t;
	$str  =~ s/([a-fA-F0-9]{2})/chr(hex $1)/eg;
	$t = reverse($str) ;
	$t= "''".$t."''";
	$line =~ s/0hex[a-fA-F0-9]*/$t/eg ;
	}
	print $line."\n" ;
}
