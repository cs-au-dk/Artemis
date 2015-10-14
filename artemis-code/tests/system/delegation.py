#!/usr/bin/env python

"""
Test suite for features relating to event delegation.

Tests are read from FIXTURE_ROOT and should include their expected output from Artemis in the first lines, as we do for
the concolic.py tests.
"""

import os
import unittest
import re

import concolic # This suite re-uses some of the concolic test harness infrastructure.
from harness.artemis import execute_artemis


FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/event-delegation/')



class EventDelegation(unittest.TestCase):
    pass


def list_delegation_tests(folder):
    """
    Lists the delegation test case pages and the tests they include.
    Delegation test pages are stored in <folder>/<test-name>/index.html.
    """
    out = []

    # Grab all the tests in FIXTURE_ROOT
    for test_name in os.listdir(folder):
        # Ignore those with '_' or '%' prefixes, and without an index.html.
        index_file = os.path.join(folder, test_name, "index.html")
        if not os.path.isfile(index_file) or test_name[0:1] == "_" or test_name[0:1] == "%":
            continue
        
        result = {"test": {}, "i_test": {}, "name": test_name, 'fn': os.path.join(test_name, "index.html"), "expected_failure": False}
        with open(index_file, 'r') as fl:
            if re.match("^\s*<!--\s*$", fl.readline()):
                for line in fl:
                    ef = re.match("^\s*EXPECTED_FAILURE", line)
                    if ef:
                        result["expected_failure"] = True
                        continue
                    
                    m = re.match("\s*TEST(_INTERN)? ([^<>!=\s]+)\s*((<|>|=|!)=?)([^=].*)$", line)
                    if not m:
                        continue
                    
                    test_mode = "i_test" if m.group(1) else "test"
                    
                    op = {"<": "lt", "<=": "leq", ">": "gt", ">=": "geq", "==": "eq", "=": "eq", "!": "neq",
                          "!=": "neq"}[m.group(3)]
                    if op not in result[test_mode]:
                        result[test_mode][op] = {}
                    
                    result[test_mode][op][m.group(2).strip()] = m.group(5).strip()
                    
                    if re.match("-->", line):
                        break

        if len(result['test']) == 0:
            result['test'] = None
        if len(result['i_test']) == 0:
            result['i_test'] = None
        out.append(result)
    
    return out


def _artemis_runner_no_injections(name, path):
    return execute_artemis(name, path,
                           iterations=2,
                           debug_concolic=' ',
                           verbose=False)

def _artemis_runner_full(name, path):
    return execute_artemis(name, path,
                           iterations=10,
                           debug_concolic=' ',
                           strategy_target_selection='concolic',
                           verbose=False)


def main():
    test_cases = list_delegation_tests(FIXTURE_ROOT)
    
    # Generate the 'constraint-solving-without-injection' tests.
    # These replace the TargetSolverNoInjection tests we used to have in test.py.
    constraint_solved_tests = {
            "eq": {
                #"Concolic::Solver::ErrorsReadingSolution": "0",    # Error by default, don't neet to test explicitly.
                #"Concolic::Solver::ConstraintsSolvedAsUNSAT": "0", # Error by default, don't neet to test explicitly.
                #"Concolic::Solver::ConstraintsNotSolved": "0",     # Error by default, don't neet to test explicitly.
                "Concolic::Solver::ConstraintsSolved": "1"
            }
        }
    
    for t in test_cases:
        test_name = 'test_constraint-solving-without-injection_%s' % t['name']
        file_name = "%s%s" % (FIXTURE_ROOT, t['fn'])
        test = concolic.test_generator(_artemis_runner_no_injections, file_name, test_name, test_dict=constraint_solved_tests, internal_test=None)
        setattr(EventDelegation, test_name, test)
    
    # Generate the tests which check for the assertions included in the test suite.
    for t in test_cases:
        test_name = 'test_%s' % t['name']
        file_name = "%s%s" % (FIXTURE_ROOT, t['fn'])
        
        test = concolic.test_generator(_artemis_runner_full, file_name, test_name, test_dict=t['test'], internal_test=t['i_test'])
        
        if t['expected_failure']:
            test = unittest.expectedFailure(test)
        
        setattr(EventDelegation, test_name, test)
    
    unittest.main(buffer=True, catchbreak=True)
    

if __name__ == "__main__":
    main()

