#!/usr/bin/env python

import os

FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/solver/')

TWO_VARIABLES_TEMPLATE_FILE = FIXTURE_ROOT + '/%symbolic_test_two_variables.html'

import sys
import unittest
import re
import subprocess

from harness.environment import WebServer
from harness.artemis import execute_artemis
from os import listdir
from os.path import isfile, join

class Solver(unittest.TestCase):
    pass

def test_generator(test_name, test_filename):
    
    def test(self):

        def _fetch_and_inject(fields, report):
        
            string_fields = []
            boolean_fields = []
            integer_fields = []
        
            for field_name in fields:

                value = report.get("Concolic::Solver::Constraint.SYM_IN_%s" % field_name, None)

                if value is not None:
                    value = str(value).replace('"', '')
                    string_fields.append("#%s=%s" % (field_name, value))
                    continue

                value = report.get("Concolic::Solver::Constraint.SYM_IN_BOOL_%s" % field_name, None)

                if value is not None:
                    value = str(value)
                    value = 'true' if value == 'True' else 'false' if value == 'False' else value
                    boolean_fields.append("#%s=%s" % (field_name, value))
                    continue

                value = report.get("Concolic::Solver::Constraint.SYM_IN_INT_%s" % field_name, None)

                if value is not None:
                    integer_fields.append("#%s=%s" % (field_name, str(value)))
                    continue

                string_fields.append("#%s=%s" % (field_name, 0))

            return string_fields, boolean_fields, integer_fields

        unsat = 'unsat' in test_filename
        unsupported = 'unsupported' in test_filename

        fields = ("testinputx", "testinputy", "testinputNameId", "testinputId", "testinputfoo", "testinputbar", "booleaninput", "selectinput", "radio1a", "radio1b", "radio1c", "testinputselect")

        report = execute_artemis(test_name, "%s/%s" % (FIXTURE_ROOT, test_filename), 
                                 iterations=2,
                                 boolean_fields=["#booleaninput=true", "#radio1b=true", "#radio1a=false", "#radio1c=false"],
                                 string_fields=["#testinputx=1", "#testinputy=2", "#testinputNameId=1", "#testinputId=1", "#testinputfoo=foo", "#testinputbar=bar", "#selectinput=Select1", "#testinputselect=volvo"],
                                 verbose=True)

        assert report.get('WebKit::alerts', 0) == 1, "Initial execution did not reach a print statement"

        if unsat:
            assert report.get('Concolic::Solver::ConstraintsSolvedAsUNSAT', 0) == 1, "Initial execution did not return as UNSAT"
            return
        elif unsupported:
            assert report.get('Concolic::Solver::ConstraintsSolved', 0) == 0, "Initial execution did not return as unsupported"
            return
        else:
            assert report.get('Concolic::Solver::ConstraintsSolvedAsUNSAT', 0) == 0, "Initial execution returned as UNSAT"
            assert report.get('Concolic::Solver::ConstraintsSolved', 0) == 1, "Initial execution did not solve a constraint"

	assert report.get('Concolic::Solver::ErrorsReadingSolution', 0) == 0, "Errors reading the solver solution"

        string_fields, boolean_fields, integer_fields = _fetch_and_inject(fields, report)
            
        report = execute_artemis(test_name, "%s/%s" % (FIXTURE_ROOT, test_filename),
                                 iterations=2,       
                                 boolean_fields=boolean_fields,
                                 string_fields=string_fields,
                                 integer_fields=integer_fields,
                                 reverse_constraint_solver=True,
                                 verbose=True)

        assert report.get('WebKit::alerts', 0) == 1, "Execution using inputs from the solver did not reach a print statement... STRING: %s, BOOLEAN: %s, INTEGER: %s" % (string_fields, boolean_fields, integer_fields)
        assert report.get('Concolic::Solver::ErrorsReadingSolution', 0) == 0, "Errors reading the solver solution"

        # negative case
    
        string_fields, boolean_fields, integer_fields = _fetch_and_inject(fields, report)

        report = execute_artemis(test_name, "%s/%s" % (FIXTURE_ROOT, test_filename),
                             iterations=2,              
                             boolean_fields=boolean_fields,
                             string_fields=string_fields,
                             integer_fields=integer_fields,
                             reverse_constraint_solver=True,
                             verbose=True)

        assert report.get('Concolic::Solver::ErrorsReadingSolution', 0) == 0, "Errors reading the solver solution"
        assert report.get('Concolic::Solver::ConstraintsSolvedAsUNSAT', 0) == 0, "NEGATED execution returned as UNSAT"
        assert report.get('Concolic::Solver::ConstraintsSolved', 0) == 1, "NEGATED execution did not solve a constraint"
        assert report.get('WebKit::alerts', 0) == 0, "NEGATED execution REACHED a print statement when it should not using STRING: %s, BOOLEAN: %s, INTEGER: %s" % (string_fields, boolean_fields, integer_fields)

    return test

def _insert_test_into_template(path, filename):
    tmpName = ".%s.html" % filename
    tmpPath = join(path, tmpName)
    with open(tmpPath, 'w') as targetFile:
        with open(TWO_VARIABLES_TEMPLATE_FILE, 'r') as templateFile:
            for line in templateFile.readlines():
                i = line.find('$TESTSTATEMENT')
                if i >= 0:
                    targetFile.write(line[0:i])
                    with open(join(path, filename), 'r') as testFile:
                        targetFile.writelines(testFile.readlines())
                        targetFile.write(line[i + 14:])
                else:
                    targetFile.write(line)
    
    return tmpName


def _list_tests_in_folder(folder):
    out = []

    for f in listdir(folder):
        p = join(folder, f)

        if not isfile(p) or f[0:1] == "." or f[0:1] == "%" or '~' in f or '#' in f:
            continue

        out.append(f)

    return out

if __name__ == '__main__':
                                                                            
    for raw_filename in _list_tests_in_folder(FIXTURE_ROOT):
        test_filename = _insert_test_into_template(FIXTURE_ROOT, raw_filename)
        test_name = 'test_%s' % raw_filename.replace(".", "_")

        test = test_generator(test_name, test_filename)
	test.__name__ = test_name
        setattr(Solver, test_name, test)

    unittest.main(buffer=True)


