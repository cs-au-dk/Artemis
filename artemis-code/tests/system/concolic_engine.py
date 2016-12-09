#!/usr/bin/env python

import os
import unittest

from harness.artemis import execute_artemis

FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/concolic-engine/')


class ConcolicEngnie(unittest.TestCase):
    
    def test_input_functions_exist(self):
        file_name = "input-functions-exist.html"
        report = run_artemis(self._test_name(), "{}{}".format(FIXTURE_ROOT, file_name))
        
        # Check we get the expected output.
        alerts = report["alerts"]
        
        self.assertIn("typeof(artemisInputString): function", alerts)
        self.assertIn("typeof(artemisInputInteger): function", alerts)
        self.assertIn("typeof(artemisInputBoolean): function", alerts)
        
    
    def test_input_functions_default_values(self):
        file_name = "input-functions-exist.html"
        report = run_artemis(self._test_name(), "{}{}".format(FIXTURE_ROOT, file_name))
        
        # Check we get the expected output.
        alerts = report["alerts"]
        
        self.assertIn("artemisInputString('x'): ''", alerts)
        self.assertIn("artemisInputInteger('y'): 0", alerts)
        self.assertIn("artemisInputBoolean('z'): false", alerts)
        
    
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
