#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/symbolic-expression'
WEBSERVER_URL = 'http://localhost:%s' % WEBSERVER_PORT

TWO_VARIABLES_TEMPLATE_FILE = WEBSERVER_ROOT+'/_symbolic_test_two_variables.html'

import unittest
import re

from harness.environment import WebServer
from harness.artemis import execute_artemis
from os import listdir
from os.path import isfile, join


class TestSequence(unittest.TestCase):
    pass


def test_generator(filename, name, path_condition):
    def test(self):
        newFilename = setupTempFile(WEBSERVER_ROOT, filename)
        report = execute_artemis(name, "{0}/{1}".format(WEBSERVER_URL, newFilename), iterations=5)
        self.assertTrue(len(report['pathCondition']) > 0)
        pc = report['pathCondition'][-1]
        self.assertEqual(path_condition.replace(" ", ""), pc.replace(" ", ""))

    return test


def setupTempFile(path, filename):
    tmpName = "_%s" % filename
    tmpPath = join(path, tmpName)

    # always overwrite the file
    with open(tmpPath, 'w') as tf:
        with open(join(path, filename), 'r') as ff:
            lines = ff.readlines()
            for line in lines[1:]:
                tf.write(line)
    return tmpName


def generate_tests_from_folder(folder):
    out = []
    for f in listdir(folder):
        p = join(folder, f)
        if isfile(p) and f[0:1] != "_":
            with open(p, 'r') as fl:
                first_line = fl.readline()
                m = re.match("\s*TEST PC:(.+)$", first_line)
                if m:
                    if f[-5:] == '.html':
                        res = {'path_condition': m.group(1), 'file_name': f, 'type': 'page',
                               'name': f.replace('.', '_')}
                    else:
                        res = {'path_condition': m.group(1), 'file_name': f, 'type': 'nonPage',
                               'name': f.replace('.', '_')}
                    out.append(res)
    return out


if __name__ == '__main__':
    server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
    for t in generate_tests_from_folder(WEBSERVER_ROOT):
        test_name = 'test_%s' % t['name']
        test = test_generator(t['file_name'], t['name'], t['path_condition'])
        setattr(TestSequence, test_name, test)
    unittest.main()
    del server
