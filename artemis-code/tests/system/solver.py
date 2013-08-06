#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/constraint-solver'
WEBSERVER_URL = 'http://localhost:%s' % WEBSERVER_PORT

TWO_VARIABLES_TEMPLATE_FILE = WEBSERVER_ROOT + '/%symbolic_test_two_variables.html'

import unittest
import re

from harness.environment import WebServer
from harness.artemis import execute_artemis
from os import listdir
from os.path import isfile, join

class TestSequence(unittest.TestCase):
    pass

def generate_test(raw_filename, name, unsat):
    def test(self):
        test_filename = insert_test_into_template(WEBSERVER_ROOT, raw_filename)

        report = execute_artemis(name, "%s/%s" % (WEBSERVER_URL, test_filename), 
            iterations=2,
            fields=["#testinputx=1", "#testinputy=2", "#testinputNameId=1", "#testinputId=1", "#testinputfoo=foo", "#testinputbar=bar"])
        
        self.assertEquals(report.get('WebKit::alerts', 0), 1)        

        new_fields = []

        for field_name in ("testinputx", "testinputy", "testinputNameId", "testinputId", "testinputfoo", "testinputbar"):
            new_fields.append("#%s=%s" % (field_name, str(report.get("Concolic::Solver::Constraint.SYM_IN_%s" % field_name, 0))))

        report = execute_artemis(name, "%s/%s" % (WEBSERVER_URL, test_filename),                                                                            
            iterations=2,                                                                                                                                   
            fields=new_fields)

        if unsat:
            self.assertEquals(report.get('Concolic::Solver::ConstraintsSolved', 0), 0)
        else:
            self.assertEquals(report.get('WebKit::alerts', 0), 1)

    return test


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
        
        out.append({
                'file_name': f, 
                'name': f.replace('.', '_'),
                'unsat': 'unsat' in f
                })

    return out


if __name__ == '__main__':
    server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
    for t in list_tests_in_folder(WEBSERVER_ROOT):
        test_name = 'test_%s' % t['name']
        test = generate_test(t['file_name'], t['name'], t['unsat'])
        setattr(TestSequence, test_name, test)
    unittest.main()
    del server
