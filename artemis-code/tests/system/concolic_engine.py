#!/usr/bin/env python

import os
import unittest

from harness.artemis import execute_artemis

FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/concolic-engine/')


class ConcolicEngnie(unittest.TestCase):
    
    def test_input_functions_exist(self):
        report = run_artemis(self._test_name(), os.path.join(FIXTURE_ROOT, "input-functions-exist.js"))
        
        # Check we get the expected output.
        alerts = report["alerts"]
        
        self.assertIn("typeof(artemisInputString): function", alerts)
        self.assertIn("typeof(artemisInputInteger): function", alerts)
        self.assertIn("typeof(artemisInputBoolean): function", alerts)
        
    
    def test_input_functions_default_values(self):
        report = run_artemis(self._test_name(), os.path.join(FIXTURE_ROOT, "input-functions-exist.js"))
        
        # Check we get the expected output.
        alerts = report["alerts"]
        
        self.assertIn("artemisInputString('x'): ''", alerts)
        self.assertIn("artemisInputInteger('y'): 0", alerts)
        self.assertIn("artemisInputBoolean('z'): false", alerts)
        
    
    def test_concolic_engine(self):
        report = run_artemis(self._test_name(), os.path.join(FIXTURE_ROOT, "simple-conditions.js"))
        
        # Check we explored some branches.
        self.assertIn("Concolic::ExecutionTree::DistinctTracesExplored", report)
        self.assertEqual(report["Concolic::ExecutionTree::DistinctTracesExplored"], 8)
        
    
    def _test_name(self):
        return self.id().split(".")[-1]
    

def run_artemis(name, js_file):
    return execute_artemis(name, None,
                           iterations=0,
                           major_mode='concolic-test',
                           concolic_test_mode_js=js_file)

if __name__ == "__main__":
    unittest.main()
