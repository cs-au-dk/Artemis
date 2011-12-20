#!/usr/bin/env perl -wT
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
#                 J. Paul Reed <preed@sigkill.com>
#                 Frédéric Buclin <LpSolit@gmail.com>

use strict;
use lib qw(. lib);

use Bugzilla;
use Bugzilla::Constants;
use Bugzilla::Config qw(:admin);
use Bugzilla::Config::Common;
use Bugzilla::Hook;
use Bugzilla::Util;
use Bugzilla::Error;
use Bugzilla::Token;
use Bugzilla::User;
use Bugzilla::User::Setting;
use Bugzilla::Status;

my $user = Bugzilla->login(LOGIN_REQUIRED);
my $cgi = Bugzilla->cgi;
my $template = Bugzilla->template;
my $vars = {};

print $cgi->header();

$user->in_group('tweakparams')
  || ThrowUserError("auth_failure", {group  => "tweakparams",
                                     action => "access",
                                     object => "parameters"});

my $action = trim($cgi->param('action') || '');
my $token  = $cgi->param('token');
my $current_panel = $cgi->param('section') || 'core';
$current_panel =~ /^([A-Za-z0-9_-]+)$/;
$current_panel = $1;

my $current_module;
my @panels = ();
my $param_panels = Bugzilla::Config::param_panels();
foreach my $panel (keys %$param_panels) {
    my $module = $param_panels->{$panel};
    eval("require $module") || die $@;
    my @module_param_list = "$module"->get_param_list();
    my $item = { name => lc($panel),
                 current => ($current_panel eq lc($panel)) ? 1 : 0,
                 param_list => \@module_param_list,
                 sortkey => eval "\$${module}::sortkey;"
               };
    push(@panels, $item);
    $current_module = $panel if ($current_panel eq lc($panel));
}

$vars->{panels} = \@panels;

if ($action eq 'save' && $current_module) {
    check_token_data($token, 'edit_parameters');
    my @changes = ();
    my @module_param_list = "$param_panels->{$current_module}"->get_param_list();

    foreach my $i (@module_param_list) {
        my $name = $i->{'name'};
        my $value = $cgi->param($name);

        if (defined $cgi->param("reset-$name")) {
            $value = $i->{'default'};
        } else {
            if ($i->{'type'} eq 'm') {
                # This simplifies the code below
                $value = [ $cgi->param($name) ];
            } else {
                # Get rid of windows/mac-style line endings.
                $value =~ s/\r\n?/\n/g;
                # assume single linefeed is an empty string
                $value =~ s/^\n$//;
            }
        }

        my $changed;
        if ($i->{'type'} eq 'm') {
            my @old = sort @{Bugzilla->params->{$name}};
            my @new = sort @$value;
            if (scalar(@old) != scalar(@new)) {
                $changed = 1;
            } else {
                $changed = 0; # Assume not changed...
                for (my $cnt = 0; $cnt < scalar(@old); ++$cnt) {
                    if ($old[$cnt] ne $new[$cnt]) {
                        # entry is different, therefore changed
                        $changed = 1;
                        last;
                    }
                }
            }
        } else {
            $changed = ($value eq Bugzilla->params->{$name})? 0 : 1;
        }

        if ($changed) {
            if (exists $i->{'checker'}) {
                my $ok = $i->{'checker'}->($value, $i);
                if ($ok ne "") {
                    ThrowUserError('invalid_parameter', { name => $name, err => $ok });
                }
            } elsif ($name eq 'globalwatchers') {
                # can't check this as others, as Bugzilla::Config::Common
                # can not use Bugzilla::User
                foreach my $watcher (split(/[,\s]+/, $value)) {
                    ThrowUserError(
                        'invalid_parameter',
                        { name => $name, err => "no such user $watcher" }
                    ) unless login_to_id($watcher);
                }
            }
            push(@changes, $name);
            SetParam($name, $value);
            if (($name eq "shutdownhtml") && ($value ne "")) {
                $vars->{'shutdown_is_active'} = 1;
            }
            if ($name eq 'duplicate_or_move_bug_status') {
                Bugzilla::Status::add_missing_bug_status_transitions($value);
            }
        }
    }

    $vars->{'message'} = 'parameters_updated';
    $vars->{'param_changed'} = \@changes;

    write_params();
    delete_token($token);
}

$vars->{'token'} = issue_session_token('edit_parameters');

$template->process("admin/params/editparams.html.tmpl", $vars)
    || ThrowTemplateError($template->error());
