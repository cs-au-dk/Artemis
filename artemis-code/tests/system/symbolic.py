#!/usr/bin/env python

import os

WEBSERVER_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), './fixtures/symbolic-expression')

TWO_VARIABLES_TEMPLATE_FILE = WEBSERVER_ROOT + '/%symbolic_test_two_variables.html'

import unittest
import re

from harness.environment import WebServer
from harness.artemis import execute_artemis
from os import listdir
from os.path import isfile, join


class Symbolic(unittest.TestCase):
    pass


def test_generator(filename, name, path_condition, page):
    def test(self):
        if page:
            newFilename = setupTempFile(WEBSERVER_ROOT, filename)
        else:
            newFilename = setUpTempFileFromTemplate(WEBSERVER_ROOT, filename)

        report = execute_artemis(name, "{0}/{1}".format(WEBSERVER_ROOT, newFilename), verbose=True, iterations=2,
				fields=["#selectinput=volvo"],)
        
	if len(report['pathCondition']) > 0:
            pc = report['pathCondition'][-1]
        else:
            pc = ""

        self.assertEqual(path_condition.replace(" ", ""), pc.replace(" ", ""))

    return test


def setupTempFile(path, filename):
    tmpName = "_%s" % filename
    tmpPath = join(path, tmpName)
    with open(tmpPath, 'w') as tf:
        with open(join(path, filename), 'r') as ff:
            tf.writelines(ff.readlines()[1:])
    return tmpName


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
                m = re.match("\s*TEST PC:(.*)$", first_line)
                if m:
                    res = {'path_condition': m.group(1), 'file_name': f, 'page': f[-5:] == '.html',
                           'name': f.replace('.', '_')}

                    out.append(res)
    return out


if __name__ == '__main__':
    for t in generate_tests_from_folder(WEBSERVER_ROOT):
        test_name = 'test_%s' % t['name']
        test = test_generator(t['file_name'], t['name'], t['path_condition'], t['page'])
	test.__name__ = test_name
        setattr(Symbolic, test_name, test)
    unittest.main(buffer=True)
