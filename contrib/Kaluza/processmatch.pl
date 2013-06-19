#!/usr/bin/perl -w

#
# Author : Devdatta Akhawe
#

use File::Spec::Functions qw(rel2abs);
use File::Basename;

#pcre_tohampi.pm needs to be in the same directory as this script
use lib dirname(rel2abs($0));

use pcre_tohampi;
use strict;
use warnings; 

my $TMPPATH=$ENV{"TMPPATH"} || "/tmp";

exit unless (-e "$TMPPATH/matchvars");

open(FILE,"$TMPPATH/matchvars") or die "$TMPPATH/mathvars exists but can't open";
print "\n";
my ($regex,$str);
<FILE>; #throw away the first newline
while(<FILE>){
  chomp;
  $regex=$_;	
  chomp($str=<FILE>);
  $regex=substr $regex,6;
  $str=substr $str,6;
  #print "found regex :$regex:, and str :$str:";
  next if( $regex =~ m/^.*?g[^\/]*$/);
  $regex=~ s/@/\\@/g;
  my $creg=eval 'qr'.$regex;
  my $p=pcre_tohampi->new($creg);
  $p->parse;
  my @rules;
  @rules=$p->getmatchconstraints($str);
  my $maxnum=shift @rules;
  print "IF ($str) {\n";
  print join(";\n",@rules);
  print "\n";
  for(my $i=0;$i<=$maxnum;$i++){
      print "$str\_idx_$i \\in CapturedBrack(".$regex.",$i);\n";
      
  }
  print "\n$str\_len_0 == Len($str\_idx_0);\n$str\_len_0 < 15;\n";
  print "}\n ELSE {\n}\n";
}
  
close(FILE);
unlink("$TMPPATH/matchvars");
