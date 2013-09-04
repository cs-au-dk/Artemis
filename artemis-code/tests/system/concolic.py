#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/concolic/'
WEBSERVER_URL = 'http://localhost:%s' % WEBSERVER_PORT

import sys
import nose
import re
import subprocess

from harness.environment import WebServer
from harness.artemis import execute_artemis
from os import listdir
from os.path import isfile, join

def _run_test(test_filename, dryrun=False):
    
    name = test_filename.replace('.', '_')
    
    report = execute_artemis(name, "%s/%s" % (WEBSERVER_URL, test_filename), 
                             iterations=2,
                             major_mode='concolic',
                             dryrun=dryrun)

    if dryrun:
        # only print the command, exit
        return
        
    # insert global assertions here


def _list_tests_in_folder(folder):
    out = []

    for f in listdir(folder):
        p = join(folder, f)

        if not isfile(p) or f[0:1] == "_" or f[0:1] == "%" or '~' in f or '#' in f:
            continue
        
        out.append(f)

    return out


def test_generator():
    server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
    for t in _list_tests_in_folder(WEBSERVER_ROOT):
	yield _run_test, t
    del server


if __name__ == '__main__':
    if len(sys.argv) < 2:
        subprocess.call(['nosetests', 'concolic.py'])
    else:
        server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
        dryrun = len(sys.argv) == 3 and sys.argv[2] == "dryrun"
        _run_test(sys.argv[1], dryrun=dryrun)
        del server

