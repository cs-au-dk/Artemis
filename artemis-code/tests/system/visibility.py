#!/usr/bin/env python

"""
Test suite for features relating to element visibility.

Tests are read from FIXTURE_ROOT and should include their expected output from Artemis in the first lines, as we do for
the concolic.py tests.
"""

import os
import unittest

import concolic # This suite re-uses some of the concolic test harness infrastructure.
from harness.artemis import execute_artemis

VISIBILITY_FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/visibility/')

class Visibility(unittest.TestCase):
    pass

def _visibility_artemis_runner(name, path):
    return execute_artemis(name, path,
                           iterations=1,
                           event_visibility_check=True,
                           verbose=True)

if __name__ == '__main__':

    for t in concolic.list_tests_in_folder(VISIBILITY_FIXTURE_ROOT):
        test_name = 'test_%s' % t['fn'].replace(".", "_")
        file_name = "%s%s" % (VISIBILITY_FIXTURE_ROOT, t['fn'])
        
        test = concolic.test_generator(_visibility_artemis_runner, file_name, test_name, test_dict=t['test'], internal_test=t['i_test'])
        if t['expected_failure']:
            test = unittest.expectedFailure(test)
        
        setattr(Visibility, test_name, test)

    unittest.main(buffer=True, catchbreak=True)
