#!/usr/bin/perl

use warnings;
use strict;

while(<STDIN>){
	chomp;
	if(m/([^\ ]*)\s*(\d+)/){
		print (sprintf "$1 0hex%08X\n",$2);
	}
}
