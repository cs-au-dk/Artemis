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
# The Initial Developer of the Original Code is Everything Solved, Inc.
# Portions created by Everything Solved, Inc. are Copyright (C) 2007 
# Everything Solved, Inc. All Rights Reserved.
#
# Contributor(s): Max Kanat-Alexander <mkanat@bugzilla.org>

package extensions::example::lib::WSExample;
use strict;
use warnings;
use base qw(Bugzilla::WebService);
use Bugzilla::Error;

# This can be called as Example.hello() from XML-RPC.
sub hello { return 'Hello!'; }

sub throw_an_error { ThrowUserError('example_my_error') }

1;
