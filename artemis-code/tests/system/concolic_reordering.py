#!/usr/bin/env python

# Adapted from concolic.py

import os

FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/concolic-reordering/')

import unittest
from harness.artemis import execute_artemis
from concolic import list_tests_in_folder, test_generator


class ConcolicReordering(unittest.TestCase):
    pass


def _artemis_runner(name, path):
    return execute_artemis(name, path,
                           iterations=0,
                           major_mode='concolic-reordering',
                           event_delegation_testing=False,
                           verbose=True)


def setup_concolic_tests():

    for t in list_tests_in_folder(FIXTURE_ROOT):
        test_name = 'test_%s' % t['fn'].replace(".", "_")
        file_name = "%s%s" % (FIXTURE_ROOT, t['fn'])
        
        test = test_generator(_artemis_runner, file_name, test_name, test_dict=t['test'], internal_test=t['i_test'])
        if t['expected_failure']:
            test = unittest.expectedFailure(test)
        
        setattr(ConcolicReordering, test_name, test)



if __name__ == '__main__':
    setup_concolic_tests()
    unittest.main(buffer=True, catchbreak=True)
