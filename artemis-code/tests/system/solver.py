#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/constraint-solver'
WEBSERVER_URL = 'http://localhost:%s' % WEBSERVER_PORT

TWO_VARIABLES_TEMPLATE_FILE = WEBSERVER_ROOT + '/%symbolic_test_two_variables.html'

import sys
import nose
import re
import subprocess

from harness.environment import WebServer
from harness.artemis import execute_artemis
from os import listdir
from os.path import isfile, join

def run_test(raw_filename, dryrun=False):
    test_filename = insert_test_into_template(WEBSERVER_ROOT, raw_filename)
    
    unsat = 'unsat' in raw_filename
    name = raw_filename.replace('.', '_')
    
    report = execute_artemis(name, "%s/%s" % (WEBSERVER_URL, test_filename), 
                             iterations=2,
                             fields=["#testinputx=1", "#testinputy=2", "#testinputNameId=1", "#testinputId=1", "#testinputfoo=foo", "#testinputbar=bar"],
                             dryrun=dryrun)

    if dryrun:
        # only print the command, exit
        return
        
    assert report.get('WebKit::alerts', 0) == 1, "Initial execution did not reach a print statement"
    
    new_fields = []

    for field_name in ("testinputx", "testinputy", "testinputNameId", "testinputId", "testinputfoo", "testinputbar"):
        new_fields.append("#%s=%s" % (field_name, str(report.get("Concolic::Solver::Constraint.SYM_IN_%s" % field_name, 0))))
        
    report = execute_artemis(name, "%s/%s" % (WEBSERVER_URL, test_filename),                                                                            
                             iterations=2,              
                             fields=new_fields)

    if unsat:
        assert report.get('Concolic::Solver::ConstraintsSolved', 0) == 0, "Unexpected constraints solved in UNSAT test case"
    else:
        assert report.get('WebKit::alerts', 0) == 1, "Execution using inputs from the solver did not reach a print statement"


def insert_test_into_template(path, filename):
    tmpName = "_g_%s.html" % filename
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


def list_tests_in_folder(folder):
    out = []

    for f in listdir(folder):
        p = join(folder, f)

        if not isfile(p) or f[0:1] == "_" or f[0:1] == "%":
            continue
        
        out.append(f)

    return out


def test_generator():
    server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
    for t in list_tests_in_folder(WEBSERVER_ROOT):
	yield run_test, t
    del server


if __name__ == '__main__':
    if len(sys.argv) < 2:
        subprocess.call(['nosetests', 'solver.py'])
    else:
        dryrun = len(sys.argv) == 3 and sys.argv[2] == "dryrun"
        run_test(sys.argv[1], dryrun=dryrun)

