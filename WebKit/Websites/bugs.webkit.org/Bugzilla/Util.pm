# -*- Mode: perl; indent-tabs-mode: nil -*-
#
# The contents of this file are subject to the Mozilla Public
# License Version 1.1 (the "License"); you may not use this file
# except in compliance with the License. You may obtain a copy of
# the License at http://www.mozilla.org/MPL/
#
# Software distributed under the License is distributed on an "AS
# IS" basis, WITHOUT WARRANTY OF ANY KIND, either express or
# implied. See the License for the specific language governing
# rights and limitations under the License.
#
# The Original Code is the Bugzilla Bug Tracking System.
#
# The Initial Developer of the Original Code is Netscape Communications
# Corporation. Portions created by Netscape are
# Copyright (C) 1998 Netscape Communications Corporation. All
# Rights Reserved.
#
# Contributor(s): Terry Weissman <terry@mozilla.org>
#                 Dan Mosedale <dmose@mozilla.org>
#                 Jacob Steenhagen <jake@bugzilla.org>
#                 Bradley Baetz <bbaetz@student.usyd.edu.au>
#                 Christopher Aillon <christopher@aillon.com>
#                 Max Kanat-Alexander <mkanat@bugzilla.org>
#                 Frédéric Buclin <LpSolit@gmail.com>
#                 Marc Schumann <wurblzap@gmail.com>

package Bugzilla::Util;

use strict;

use base qw(Exporter);
@Bugzilla::Util::EXPORT = qw(is_tainted trick_taint detaint_natural
                             detaint_signed
                             html_quote url_quote xml_quote
                             css_class_quote html_light_quote url_decode
                             i_am_cgi get_netaddr correct_urlbase
                             lsearch ssl_require_redirect use_attachbase
                             diff_arrays diff_strings
                             trim wrap_hard wrap_comment find_wrap_point
                             format_time format_time_decimal validate_date
                             validate_time
                             file_mod_time is_7bit_clean
                             bz_crypt generate_random_password
                             validate_email_syntax clean_text
                             get_text disable_utf8);

use Bugzilla::Constants;

use Date::Parse;
use Date::Format;
use Text::Wrap;

# This is from the perlsec page, slightly modified to remove a warning
# From that page:
#      This function makes use of the fact that the presence of
#      tainted data anywhere within an expression renders the
#      entire expression tainted.
# Don't ask me how it works...
sub is_tainted {
    return not eval { my $foo = join('',@_), kill 0; 1; };
}

sub trick_taint {
    require Carp;
    Carp::confess("Undef to trick_taint") unless defined $_[0];
    my $match = $_[0] =~ /^(.*)$/s;
    $_[0] = $match ? $1 : undef;
    return (defined($_[0]));
}

sub detaint_natural {
    my $match = $_[0] =~ /^(\d+)$/;
    $_[0] = $match ? $1 : undef;
    return (defined($_[0]));
}

sub detaint_signed {
    my $match = $_[0] =~ /^([-+]?\d+)$/;
    $_[0] = $match ? $1 : undef;
    # Remove any leading plus sign.
    if (defined($_[0]) && $_[0] =~ /^\+(\d+)$/) {
        $_[0] = $1;
    }
    return (defined($_[0]));
}

sub html_quote {
    my ($var) = (@_);
    $var =~ s/\&/\&amp;/g;
    $var =~ s/</\&lt;/g;
    $var =~ s/>/\&gt;/g;
    $var =~ s/\"/\&quot;/g;
    return $var;
}

sub html_light_quote {
    my ($text) = @_;

    # List of allowed HTML elements having no attributes.
    my @allow = qw(b strong em i u p br abbr acronym ins del cite code var
                   dfn samp kbd big small sub sup tt dd dt dl ul li ol
                   fieldset legend);

    # Are HTML::Scrubber and HTML::Parser installed?
    eval { require HTML::Scrubber;
           require HTML::Parser;
    };

    if ($@) { # Package(s) not installed.
        my $safe = join('|', @allow);
        my $chr = chr(1);

        # First, escape safe elements.
        $text =~ s#<($safe)>#$chr$1$chr#go;
        $text =~ s#</($safe)>#$chr/$1$chr#go;
        # Now filter < and >.
        $text =~ s#<#&lt;#g;
        $text =~ s#>#&gt;#g;
        # Restore safe elements.
        $text =~ s#$chr/($safe)$chr#</$1>#go;
        $text =~ s#$chr($safe)$chr#<$1>#go;
        return $text;
    }
    else { # Packages installed.
        # We can be less restrictive. We can accept elements with attributes.
        push(@allow, qw(a blockquote q span));

        # Allowed protocols.
        my $safe_protocols = join('|', SAFE_PROTOCOLS);
        my $protocol_regexp = qr{(^(?:$safe_protocols):|^[^:]+$)}i;

        # Deny all elements and attributes unless explicitly authorized.
        my @default = (0 => {
                             id    => 1,
                             name  => 1,
                             class => 1,
                             '*'   => 0, # Reject all other attributes.
                            }
                       );

        # Specific rules for allowed elements. If no specific rule is set
        # for a given element, then the default is used.
        my @rules = (a => {
                           href  => $protocol_regexp,
                           title => 1,
                           id    => 1,
                           name  => 1,
                           class => 1,
                           '*'   => 0, # Reject all other attributes.
                          },
                     blockquote => {
                                    cite => $protocol_regexp,
                                    id    => 1,
                                    name  => 1,
                                    class => 1,
                                    '*'  => 0, # Reject all other attributes.
                                   },
                     'q' => {
                             cite => $protocol_regexp,
                             id    => 1,
                             name  => 1,
                             class => 1,
                             '*'  => 0, # Reject all other attributes.
                          },
                    );

        my $scrubber = HTML::Scrubber->new(default => \@default,
                                           allow   => \@allow,
                                           rules   => \@rules,
                                           comment => 0,
                                           process => 0);

        return $scrubber->scrub($text);
    }
}

# This originally came from CGI.pm, by Lincoln D. Stein
sub url_quote {
    my ($toencode) = (@_);
    utf8::encode($toencode) # The below regex works only on bytes
        if Bugzilla->params->{'utf8'} && utf8::is_utf8($toencode);
    $toencode =~ s/([^a-zA-Z0-9_\-.])/uc sprintf("%%%02x",ord($1))/eg;
    return $toencode;
}

sub css_class_quote {
    my ($toencode) = (@_);
    $toencode =~ s/ /_/g;
    $toencode =~ s/([^a-zA-Z0-9_\-.])/uc sprintf("&#x%x;",ord($1))/eg;
    return $toencode;
}

sub xml_quote {
    my ($var) = (@_);
    $var =~ s/\&/\&amp;/g;
    $var =~ s/</\&lt;/g;
    $var =~ s/>/\&gt;/g;
    $var =~ s/\"/\&quot;/g;
    $var =~ s/\'/\&apos;/g;
    
    # the following nukes characters disallowed by the XML 1.0
    # spec, Production 2.2. 1.0 declares that only the following 
    # are valid:
    # (#x9 | #xA | #xD | [#x20-#xD7FF] | [#xE000-#xFFFD] | [#x10000-#x10FFFF])
    $var =~ s/([\x{0001}-\x{0008}]|
               [\x{000B}-\x{000C}]|
               [\x{000E}-\x{001F}]|
               [\x{D800}-\x{DFFF}]|
               [\x{FFFE}-\x{FFFF}])//gx;
    return $var;
}

# This function must not be relied upon to return a valid string to pass to
# the DB or the user in UTF-8 situations. The only thing you  can rely upon
# it for is that if you url_decode a string, it will url_encode back to the 
# exact same thing.
sub url_decode {
    my ($todecode) = (@_);
    $todecode =~ tr/+/ /;       # pluses become spaces
    $todecode =~ s/%([0-9a-fA-F]{2})/pack("c",hex($1))/ge;
    return $todecode;
}

sub i_am_cgi {
    # I use SERVER_SOFTWARE because it's required to be
    # defined for all requests in the CGI spec.
    return exists $ENV{'SERVER_SOFTWARE'} ? 1 : 0;
}

sub ssl_require_redirect {
    my $method = shift;

    # If currently not in a protected SSL 
    # connection, determine if a redirection is 
    # needed based on value in Bugzilla->params->{ssl}.
    # If we are already in a protected connection or
    # sslbase is not set then no action is required.
    if (uc($ENV{'HTTPS'}) ne 'ON' 
        && $ENV{'SERVER_PORT'} != 443 
        && Bugzilla->params->{'sslbase'} ne '')
    {
        # System is configured to never require SSL 
        # so no redirection is needed.
        return 0 
            if Bugzilla->params->{'ssl'} eq 'never';
            
        # System is configured to always require a SSL
        # connection so we need to redirect.
        return 1
            if Bugzilla->params->{'ssl'} eq 'always';

        # System is configured such that if we are inside
        # of an authenticated session, then we need to make
        # sure that all of the connections are over SSL. Non
        # authenticated sessions SSL is not mandatory.
        # For XMLRPC requests, if the method is User.login
        # then we always want the connection to be over SSL
        # if the system is configured for authenticated
        # sessions since the user's username and password
        # will be passed before the user is logged in.
        return 1 
            if Bugzilla->params->{'ssl'} eq 'authenticated sessions'
                && (Bugzilla->user->id 
                    || (defined $method && $method eq 'User.login'));
    }

    return 0;
}

sub correct_urlbase {
    my $ssl = Bugzilla->params->{'ssl'};
    return Bugzilla->params->{'urlbase'} if $ssl eq 'never';

    my $sslbase = Bugzilla->params->{'sslbase'};
    if ($sslbase) {
        return $sslbase if $ssl eq 'always';
        # Authenticated Sessions
        return $sslbase if Bugzilla->user->id;
    }

    # Set to "authenticated sessions" but nobody's logged in, or
    # sslbase isn't set.
    return Bugzilla->params->{'urlbase'};
}

sub use_attachbase {
    my $attachbase = Bugzilla->params->{'attachment_base'};
    return ($attachbase ne ''
            && $attachbase ne Bugzilla->params->{'urlbase'}
            && $attachbase ne Bugzilla->params->{'sslbase'}) ? 1 : 0;
}

sub lsearch {
    my ($list,$item) = (@_);
    my $count = 0;
    foreach my $i (@$list) {
        if ($i eq $item) {
            return $count;
        }
        $count++;
    }
    return -1;
}

sub diff_arrays {
    my ($old_ref, $new_ref) = @_;

    my @old = @$old_ref;
    my @new = @$new_ref;

    # For each pair of (old, new) entries:
    # If they're equal, set them to empty. When done, @old contains entries
    # that were removed; @new contains ones that got added.
    foreach my $oldv (@old) {
        foreach my $newv (@new) {
            next if ($newv eq '');
            if ($oldv eq $newv) {
                $newv = $oldv = '';
            }
        }
    }

    my @removed = grep { $_ ne '' } @old;
    my @added = grep { $_ ne '' } @new;
    return (\@removed, \@added);
}

sub trim {
    my ($str) = @_;
    if ($str) {
      $str =~ s/^\s+//g;
      $str =~ s/\s+$//g;
    }
    return $str;
}

sub diff_strings {
    my ($oldstr, $newstr) = @_;

    # Split the old and new strings into arrays containing their values.
    $oldstr =~ s/[\s,]+/ /g;
    $newstr =~ s/[\s,]+/ /g;
    my @old = split(" ", $oldstr);
    my @new = split(" ", $newstr);

    my ($rem, $add) = diff_arrays(\@old, \@new);

    my $removed = join (", ", @$rem);
    my $added = join (", ", @$add);

    return ($removed, $added);
}

sub wrap_comment {
    my ($comment, $cols) = @_;
    my $wrappedcomment = "";

    # Use 'local', as recommended by Text::Wrap's perldoc.
    local $Text::Wrap::columns = $cols || COMMENT_COLS_WRAP;
    # Make words that are longer than COMMENT_COLS_WRAP not wrap.
    local $Text::Wrap::huge    = 'overflow';
    # Don't mess with tabs.
    local $Text::Wrap::unexpand = 0;

    # If the line starts with ">", don't wrap it. Otherwise, wrap.
    foreach my $line (split(/\r\n|\r|\n/, $comment)) {
      if ($line =~ qr/^>/) {
        $wrappedcomment .= ($line . "\n");
      }
      else {
        # Due to a segfault in Text::Tabs::expand() when processing tabs with
        # Unicode (see http://rt.perl.org/rt3/Public/Bug/Display.html?id=52104),
        # we have to remove tabs before processing the comment. This restriction
        # can go away when we require Perl 5.8.9 or newer.
        $line =~ s/\t/    /g;
        $wrappedcomment .= (wrap('', '', $line) . "\n");
      }
    }

    chomp($wrappedcomment); # Text::Wrap adds an extra newline at the end.
    return $wrappedcomment;
}

sub find_wrap_point {
    my ($string, $maxpos) = @_;
    if (!$string) { return 0 }
    if (length($string) < $maxpos) { return length($string) }
    my $wrappoint = rindex($string, ",", $maxpos); # look for comma
    if ($wrappoint < 0) {  # can't find comma
        $wrappoint = rindex($string, " ", $maxpos); # look for space
        if ($wrappoint < 0) {  # can't find space
            $wrappoint = rindex($string, "-", $maxpos); # look for hyphen
            if ($wrappoint < 0) {  # can't find hyphen
                $wrappoint = $maxpos;  # just truncate it
            } else {
                $wrappoint++; # leave hyphen on the left side
            }
        }
    }
    return $wrappoint;
}

sub wrap_hard {
    my ($string, $columns) = @_;
    local $Text::Wrap::columns = $columns;
    local $Text::Wrap::unexpand = 0;
    local $Text::Wrap::huge = 'wrap';
    
    my $wrapped = wrap('', '', $string);
    chomp($wrapped);
    return $wrapped;
}

sub format_time {
    my ($date, $format) = @_;

    # If $format is undefined, try to guess the correct date format.    
    my $show_timezone;
    if (!defined($format)) {
        if ($date =~ m/^(\d{4})[-\.](\d{2})[-\.](\d{2}) (\d{2}):(\d{2})(:(\d{2}))?$/) {
            my $sec = $7;
            if (defined $sec) {
                $format = "%Y-%m-%d %T";
            } else {
                $format = "%Y-%m-%d %R";
            }
        } else {
            # Default date format. See Date::Format for other formats available.
            $format = "%Y-%m-%d %R";
        }
        # By default, we want the timezone to be displayed.
        $show_timezone = 1;
    }
    else {
        # Search for %Z or %z, meaning we want the timezone to be displayed.
        # Till bug 182238 gets fixed, we assume Bugzilla->params->{'timezone'}
        # is used.
        $show_timezone = ($format =~ s/\s?%Z$//i);
    }

    # str2time($date) is undefined if $date has an invalid date format.
    my $time = str2time($date);

    if (defined $time) {
        $date = time2str($format, $time);
        $date .= " " . Bugzilla->params->{'timezone'} if $show_timezone;
    }
    else {
        # Don't let invalid (time) strings to be passed to templates!
        $date = '';
    }
    return trim($date);
}

sub format_time_decimal {
    my ($time) = (@_);

    my $newtime = sprintf("%.2f", $time);

    if ($newtime =~ /0\Z/) {
        $newtime = sprintf("%.1f", $time);
    }

    return $newtime;
}

sub file_mod_time {
    my ($filename) = (@_);
    my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
        $atime,$mtime,$ctime,$blksize,$blocks)
        = stat($filename);
    return $mtime;
}

sub bz_crypt {
    my ($password) = @_;

    # The list of characters that can appear in a salt.  Salts and hashes
    # are both encoded as a sequence of characters from a set containing
    # 64 characters, each one of which represents 6 bits of the salt/hash.
    # The encoding is similar to BASE64, the difference being that the
    # BASE64 plus sign (+) is replaced with a forward slash (/).
    my @saltchars = (0..9, 'A'..'Z', 'a'..'z', '.', '/');

    # Generate the salt.  We use an 8 character (48 bit) salt for maximum
    # security on systems whose crypt uses MD5.  Systems with older
    # versions of crypt will just use the first two characters of the salt.
    my $salt = '';
    for ( my $i=0 ; $i < 8 ; ++$i ) {
        $salt .= $saltchars[rand(64)];
    }

    # Wide characters cause crypt to die
    if (Bugzilla->params->{'utf8'}) {
        utf8::encode($password) if utf8::is_utf8($password);
    }
    
    # Crypt the password.
    my $cryptedpassword = crypt($password, $salt);

    # Return the crypted password.
    return $cryptedpassword;
}

# If you want to understand the security of strings generated by this
# function, here's a quick formula that will help you estimate:
# We pick from 62 characters, which is close to 64, which is 2^6.
# So 8 characters is (2^6)^8 == 2^48 combinations. Just multiply 6
# by the number of characters you generate, and that gets you the equivalent
# strength of the string in bits.
sub generate_random_password {
    my $size = shift || 10; # default to 10 chars if nothing specified
    my $rand;
    if (eval { require Math::Random::Secure; 1; }) {
        $rand = \&Math::Random::Secure::irand;
    }
    else {
        # For details on why this block works the way it does, see bug 619594.
        # (Note that we don't do this if Math::Random::Secure is installed,
        # because we don't need to.)
        my $counter = 0;
        $rand = sub {
            # If we regenerate the seed every 5 characters, our seed is roughly
            # as strong (in terms of bit size) as our randomly-generated
            # string itself.
            _do_srand() if ($counter % 5) == 0;
            $counter++;
            return int(rand $_[0]);
        };
    }
    return join("", map{ ('0'..'9','a'..'z','A'..'Z')[$rand->(62)] } 
                       (1..$size));
}

sub _do_srand {
    # On Windows, calling srand over and over in the same process produces
    # very bad results. We need a stronger seed.
    if (ON_WINDOWS) {
        require Win32;
        # GuidGen generates random data via Windows's CryptGenRandom
        # interface, which is documented as being cryptographically secure.
        my $guid = Win32::GuidGen();
        # GUIDs look like:
        # {09531CF1-D0C7-4860-840C-1C8C8735E2AD}
        $guid =~ s/[-{}]+//g;
        # Get a 32-bit integer using the first eight hex digits.
        my $seed = hex(substr($guid, 0, 8));
        srand($seed);
        return;
    }

    # On *nix-like platforms, this uses /dev/urandom, so the seed changes
    # enough on every invocation.
    srand();
}

sub validate_email_syntax {
    my ($addr) = @_;
    my $match = Bugzilla->params->{'emailregexp'};
    my $ret = ($addr =~ /$match/ && $addr !~ /[\\\(\)<>&,;:"\[\] \t\r\n]/);
    if ($ret) {
        # We assume these checks to suffice to consider the address untainted.
        trick_taint($_[0]);
    }
    return $ret ? 1 : 0;
}

sub validate_date {
    my ($date) = @_;
    my $date2;

    # $ts is undefined if the parser fails.
    my $ts = str2time($date);
    if ($ts) {
        $date2 = time2str("%Y-%m-%d", $ts);

        $date =~ s/(\d+)-0*(\d+?)-0*(\d+?)/$1-$2-$3/; 
        $date2 =~ s/(\d+)-0*(\d+?)-0*(\d+?)/$1-$2-$3/;
    }
    my $ret = ($ts && $date eq $date2);
    return $ret ? 1 : 0;
}

sub validate_time {
    my ($time) = @_;
    my $time2;

    # $ts is undefined if the parser fails.
    my $ts = str2time($time);
    if ($ts) {
        $time2 = time2str("%H:%M:%S", $ts);
        if ($time =~ /^(\d{1,2}):(\d\d)(?::(\d\d))?$/) {
            $time = sprintf("%02d:%02d:%02d", $1, $2, $3 || 0);
        }
    }
    my $ret = ($ts && $time eq $time2);
    return $ret ? 1 : 0;
}

sub is_7bit_clean {
    return $_[0] !~ /[^\x20-\x7E\x0A\x0D]/;
}

sub clean_text {
    my ($dtext) = shift;
    $dtext =~  s/[\x00-\x1F\x7F]+/ /g;   # change control characters into a space
    return trim($dtext);
}

sub get_text {
    my ($name, $vars) = @_;
    my $template = Bugzilla->template_inner;
    $vars ||= {};
    $vars->{'message'} = $name;
    my $message;
    $template->process('global/message.txt.tmpl', $vars, \$message)
        || ThrowTemplateError($template->error());
    # Remove the indenting that exists in messages.html.tmpl.
    $message =~ s/^    //gm;
    return $message;
}


sub get_netaddr {
    my $ipaddr = shift;

    # Check for a valid IPv4 addr which we know how to parse
    if (!$ipaddr || $ipaddr !~ /^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/) {
        return undef;
    }

    my $addr = unpack("N", pack("CCCC", split(/\./, $ipaddr)));

    my $maskbits = Bugzilla->params->{'loginnetmask'};

    # Make Bugzilla ignore the IP address if loginnetmask is set to 0
    return "0.0.0.0" if ($maskbits == 0);

    $addr >>= (32-$maskbits);

    $addr <<= (32-$maskbits);
    return join(".", unpack("CCCC", pack("N", $addr)));
}

sub disable_utf8 {
    if (Bugzilla->params->{'utf8'}) {
        binmode STDOUT, ':bytes'; # Turn off UTF8 encoding.
    }
}

1;

__END__

=head1 NAME

Bugzilla::Util - Generic utility functions for bugzilla

=head1 SYNOPSIS

  use Bugzilla::Util;

  # Functions for dealing with variable tainting
  $rv = is_tainted($var);
  trick_taint($var);
  detaint_natural($var);
  detaint_signed($var);

  # Functions for quoting
  html_quote($var);
  url_quote($var);
  xml_quote($var);

  # Functions for decoding
  $rv = url_decode($var);

  # Functions that tell you about your environment
  my $is_cgi   = i_am_cgi();
  my $net_addr = get_netaddr($ip_addr);
  my $urlbase  = correct_urlbase();

  # Functions for searching
  $loc = lsearch(\@arr, $val);

  # Data manipulation
  ($removed, $added) = diff_arrays(\@old, \@new);

  # Functions for manipulating strings
  $val = trim(" abc ");
  ($removed, $added) = diff_strings($old, $new);
  $wrapped = wrap_comment($comment);

  # Functions for formatting time
  format_time($time);

  # Functions for dealing with files
  $time = file_mod_time($filename);

  # Cryptographic Functions
  $crypted_password = bz_crypt($password);
  $new_password = generate_random_password($password_length);

  # Validation Functions
  validate_email_syntax($email);
  validate_date($date);

=head1 DESCRIPTION

This package contains various utility functions which do not belong anywhere
else.

B<It is not intended as a general dumping group for something which
people feel might be useful somewhere, someday>. Do not add methods to this
package unless it is intended to be used for a significant number of files,
and it does not belong anywhere else.

=head1 FUNCTIONS

This package provides several types of routines:

=head2 Tainting

Several functions are available to deal with tainted variables. B<Use these
with care> to avoid security holes.

=over 4

=item C<is_tainted>

Determines whether a particular variable is tainted

=item C<trick_taint($val)>

Tricks perl into untainting a particular variable.

Use trick_taint() when you know that there is no way that the data
in a scalar can be tainted, but taint mode still bails on it.

B<WARNING!! Using this routine on data that really could be tainted defeats
the purpose of taint mode.  It should only be used on variables that have been
sanity checked in some way and have been determined to be OK.>

=item C<detaint_natural($num)>

This routine detaints a natural number. It returns a true value if the
value passed in was a valid natural number, else it returns false. You
B<MUST> check the result of this routine to avoid security holes.

=item C<detaint_signed($num)>

This routine detaints a signed integer. It returns a true value if the
value passed in was a valid signed integer, else it returns false. You
B<MUST> check the result of this routine to avoid security holes.

=back

=head2 Quoting

Some values may need to be quoted from perl. However, this should in general
be done in the template where possible.

=over 4

=item C<html_quote($val)>

Returns a value quoted for use in HTML, with &, E<lt>, E<gt>, and E<34> being
replaced with their appropriate HTML entities.

=item C<html_light_quote($val)>

Returns a string where only explicitly allowed HTML elements and attributes
are kept. All HTML elements and attributes not being in the whitelist are either
escaped (if HTML::Scrubber is not installed) or removed.

=item C<url_quote($val)>

Quotes characters so that they may be included as part of a url.

=item C<css_class_quote($val)>

Quotes characters so that they may be used as CSS class names. Spaces
are replaced by underscores.

=item C<xml_quote($val)>

This is similar to C<html_quote>, except that ' is escaped to &apos;. This
is kept separate from html_quote partly for compatibility with previous code
(for &apos;) and partly for future handling of non-ASCII characters.

=item C<url_decode($val)>

Converts the %xx encoding from the given URL back to its original form.

=back

=head2 Environment and Location

Functions returning information about your environment or location.

=over 4

=item C<i_am_cgi()>

Tells you whether or not you are being run as a CGI script in a web
server. For example, it would return false if the caller is running
in a command-line script.

=item C<get_netaddr($ipaddr)>

Given an IP address, this returns the associated network address, using
C<Bugzilla->params->{'loginnetmask'}> as the netmask. This can be used
to obtain data in order to restrict weak authentication methods (such as
cookies) to only some addresses.

=item C<correct_urlbase()>

Returns either the C<sslbase> or C<urlbase> parameter, depending on the
current setting for the C<ssl> parameter.

=item C<use_attachbase()>

Returns true if an alternate host is used to display attachments; false
otherwise.

=back

=head2 Searching

Functions for searching within a set of values.

=over 4

=item C<lsearch($list, $item)>

Returns the position of C<$item> in C<$list>. C<$list> must be a list
reference.

If the item is not in the list, returns -1.

=back

=head2 Data Manipulation

=over 4

=item C<diff_arrays(\@old, \@new)>

 Description: Takes two arrayrefs, and will tell you what it takes to 
              get from @old to @new.
 Params:      @old = array that you are changing from
              @new = array that you are changing to
 Returns:     A list of two arrayrefs. The first is a reference to an 
              array containing items that were removed from @old. The
              second is a reference to an array containing items
              that were added to @old. If both returned arrays are 
              empty, @old and @new contain the same values.

=back

=head2 String Manipulation

=over 4

=item C<trim($str)>

Removes any leading or trailing whitespace from a string. This routine does not
modify the existing string.

=item C<diff_strings($oldstr, $newstr)>

Takes two strings containing a list of comma- or space-separated items
and returns what items were removed from or added to the new one, 
compared to the old one. Returns a list, where the first entry is a scalar
containing removed items, and the second entry is a scalar containing added
items.

=item C<wrap_hard($string, $size)>

Wraps a string, so that a line is I<never> longer than C<$size>.
Returns the string, wrapped.

=item C<wrap_comment($comment)>

Takes a bug comment, and wraps it to the appropriate length. The length is
currently specified in C<Bugzilla::Constants::COMMENT_COLS_WRAP>. Lines beginning
with ">" are assumed to be quotes, and they will not be wrapped.

The intended use of this function is to wrap comments that are about to be
displayed or emailed. Generally, wrapped text should not be stored in the
database.

=item C<find_wrap_point($string, $maxpos)>

Search for a comma, a whitespace or a hyphen to split $string, within the first
$maxpos characters. If none of them is found, just split $string at $maxpos.
The search starts at $maxpos and goes back to the beginning of the string.

=item C<is_7bit_clean($str)>

Returns true is the string contains only 7-bit characters (ASCII 32 through 126,
ASCII 10 (LineFeed) and ASCII 13 (Carrage Return).

=item C<disable_utf8()>

Disable utf8 on STDOUT (and display raw data instead).

=item C<clean_text($str)>
Returns the parameter "cleaned" by exchanging non-printable characters with spaces.
Specifically characters (ASCII 0 through 31) and (ASCII 127) will become ASCII 32 (Space).

=item C<get_text>

=over

=item B<Description>

This is a method of getting localized strings within Bugzilla code.
Use this when you don't want to display a whole template, you just
want a particular string.

It uses the F<global/message.txt.tmpl> template to return a string.

=item B<Params>

=over

=item C<$message> - The identifier for the message.

=item C<$vars> - A hashref. Any variables you want to pass to the template.

=back

=item B<Returns>

A string.

=back

=back

=head2 Formatting Time

=over 4

=item C<format_time($time)>

Takes a time, converts it to the desired format and appends the timezone
as defined in editparams.cgi, if desired. This routine will be expanded
in the future to adjust for user preferences regarding what timezone to
display times in.

This routine is mainly called from templates to filter dates, see
"FILTER time" in Templates.pm. In this case, $format is undefined and
the routine has to "guess" the date format that was passed to $dbh->sql_date_format().


=item C<format_time_decimal($time)>

Returns a number with 2 digit precision, unless the last digit is a 0. Then it 
returns only 1 digit precision.

=back


=head2 Files

=over 4

=item C<file_mod_time($filename)>

Takes a filename and returns the modification time. It returns it in the format
of the "mtime" parameter of the perl "stat" function.

=back

=head2 Cryptography

=over 4

=item C<bz_crypt($password)>

Takes a string and returns a C<crypt>ed value for it, using a random salt.

Please always use this function instead of the built-in perl "crypt"
when initially encrypting a password.

=begin undocumented

Random salts are generated because the alternative is usually
to use the first two characters of the password itself, and since
the salt appears in plaintext at the beginning of the encrypted
password string this has the effect of revealing the first two
characters of the password to anyone who views the encrypted version.

=end undocumented

=item C<generate_random_password($password_length)>

Returns an alphanumeric string with the specified length
(10 characters by default). Use this function to generate passwords
and tokens.

=back

=head2 Validation

=over 4

=item C<validate_email_syntax($email)>

Do a syntax checking for a legal email address and returns 1 if
the check is successful, else returns 0.
Untaints C<$email> if successful.

=item C<validate_date($date)>

Make sure the date has the correct format and returns 1 if
the check is successful, else returns 0.

=back
