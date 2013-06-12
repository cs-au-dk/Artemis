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

def test_generator(filename, name, result):
    def test(self):
        newFilename = setUpTempFileFromTemplate(WEBSERVER_ROOT, filename)

        report = execute_artemis(name, "%s/%s" % (WEBSERVER_URL, newFilename), iterations=2)

        for condition in result.split(';'):
            subject, value = condition.split('=')
            self.assertEqual(report.get(subject.strip(), 0), int(value))

    return test


def setUpTempFileFromTemplate(path, filename):
    tmpName = "_g_%s.html" % filename
    tmpPath = join(path, tmpName)
    with open(tmpPath, 'w') as tf:
        with open(TWO_VARIABLES_TEMPLATE_FILE, 'r') as templateFile:
            lines = templateFile.readlines()
            for line in lines[1:]:
                i = line.find('$TESTSTATEMENT')
                if i >= 0:
                    tf.write(line[0:i])
                    with open(join(path, filename), 'r') as testFile:
                        tf.writelines(testFile.readlines()[1:])
                    tf.write(line[i + 14:])
                else:
                    tf.write(line)
    return tmpName


def generate_tests_from_folder(folder):
    out = []
    for f in listdir(folder):
        p = join(folder, f)
        if isfile(p) and f[0:1] != "_" and f[0:1] != "%":
            with open(p, 'r') as fl:
                first_line = fl.readline()
                m = re.match("\s*RESULT:(.*)$", first_line)
                if m:
                    res = {'result': m.group(1), 'file_name': f, 'name': f.replace('.', '_')}
                    out.append(res)
    return out


if __name__ == '__main__':
    server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
    for t in generate_tests_from_folder(WEBSERVER_ROOT):
        test_name = 'test_%s' % t['name']
        test = test_generator(t['file_name'], t['name'], t['result'])
        setattr(TestSequence, test_name, test)
    unittest.main()
    del server
