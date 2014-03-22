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

def test_generator(raw_filename):
    
    def test(self):

        unsat = 'unsat' in raw_filename
        unsupported = 'unsupported' in raw_filename
        name = raw_filename.replace('.', '_')

        fields = ("testinputx", "testinputy", "testinputNameId", "testinputId", "testinputfoo", "testinputbar", "booleaninput", "selectinput", "radio1a", "radio1b", "radio1c")

        report = execute_artemis(name, "%s/%s" % (FIXTURE_ROOT, test_filename), 
                                 iterations=2,
                                 fields=["#testinputx=1", "#testinputy=2", "#testinputNameId=1", "#testinputId=1", "#testinputfoo=foo", "#testinputbar=bar", "#booleaninput=checked", "#selectinput=Select1", "#radio1b=checked", "#radio1a=", "#radio1c="],
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
        
        new_fields = []

        for field_name in fields:
            value = str(report.get("Concolic::Solver::Constraint.SYM_IN_%s" % field_name, 0))
            if value == 'False' or value == '""':
                value = ''
            new_fields.append("#%s=%s" % (field_name, value))
            
        report = execute_artemis(name, "%s/%s" % (FIXTURE_ROOT, test_filename),
                                 iterations=2,              
                                 fields=new_fields,
                                 reverse_constraint_solver=True,
                                 verbose=True)

        assert report.get('WebKit::alerts', 0) == 1, "Execution using inputs from the solver did not reach a print statement... %s" % new_fields

        # negative case
    
        new_fields = []

        for field_name in fields:
            value = str(report.get("Concolic::Solver::Constraint.SYM_IN_%s" % field_name, 0))
            if value == 'False' or value == '""':
                value = ''
                new_fields.append("#%s=%s" % (field_name, value))

        report = execute_artemis(name, "%s/%s" % (FIXTURE_ROOT, test_filename),
                             iterations=2,              
                             fields=new_fields,
                             reverse_constraint_solver=True,
                             verbose=True)

        assert report.get('Concolic::Solver::ConstraintsSolvedAsUNSAT', 0) == 0, "NEGATED execution returned as UNSAT"
        assert report.get('Concolic::Solver::ConstraintsSolved', 0) == 1, "NEGATED execution did not solve a constraint"
        assert report.get('WebKit::alerts', 0) == 0, "NEGATED execution REACHED a print statement when it should not using %s" % new_fields

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

        test = test_generator(raw_filename)
        setattr(Solver, test_name, test)

    unittest.main(buffer=True)


