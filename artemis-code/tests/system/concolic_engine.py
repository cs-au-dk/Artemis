#!/usr/bin/env python

import os
import unittest

from harness.artemis import execute_artemis

FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/concolic-engine/')


class ConcolicEngnie(unittest.TestCase):
    
    def test_artemis_make_symbolic_exists(self):
        file_name = "symbolic-value-test.html"
        report = run_artemis(self._test_name(), "{}{}".format(FIXTURE_ROOT, file_name))
        
        # Check we get the expected output.
        alerts = report["alerts"]
        
        self.assertIn("typeof(artemisMakeSymbolic): function", alerts)
        self.assertIn("Before: 5", alerts)
        self.assertIn("After: 5", alerts)
        
    
    def _test_name(self):
        return self.id().split(".")[-1]
    

def run_artemis(name, path):
    return execute_artemis(name, path,
                           iterations=1, # TODO
                           debug_concolic=' ',
                           major_mode='concolic', # TODO: Make a new concolic-engine-test mode which doesn't use forms.
                           verbose=False)

if __name__ == "__main__":
    unittest.main()
