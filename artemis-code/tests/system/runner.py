#!/usr/bin/env python

import os
import sys
import signal
import subprocess
import filecmp
import shutil
import time

THIS_DIR = os.path.abspath(os.path.dirname(__file__))

ARTEMIS_EXEC = os.path.join(THIS_DIR, '..', '..', 'dist', 'artemis')

ARTEMIS_OUTPUT_DIR = os.path.join('/', 'tmp', 'artemis')

WEBSERVER_PORT = 8001

_webserver = None

class AssertFailure(Exception):
    pass

def setup_testing_env():
    global _webserver

    web_root = os.path.join(THIS_DIR, 'fixtures')

    print 'starting webserver at %s' % web_root
    _webserver = subprocess.Popen('python -m SimpleHTTPServer %s' % WEBSERVER_PORT,
                                  cwd=web_root, shell=True, preexec_fn=os.setsid)


    time.sleep(1) # allow the web-server to start before running artemis

    try:
        print 'creating result directory %s' % ARTEMIS_OUTPUT_DIR
        os.mkdir(ARTEMIS_OUTPUT_DIR)
    except OSError:
        pass

def teardown_testing_env():
    os.killpg(_webserver.pid, signal.SIGKILL)

def get_fixture_paths(fixture_name):
    output_dir = os.path.join(ARTEMIS_OUTPUT_DIR, fixture_name)
    result_dir = os.path.join(THIS_DIR, 'results', fixture_name)

    url = 'http://localhost:%s/%s/index.html' % (WEBSERVER_PORT,
                                                 fixture_name)

    return (output_dir, result_dir, url)

def execute_artemis(fixture_name, emit_output=False):

    output_dir, result_dir, url = get_fixture_paths(fixture_name)

    try:
        os.mkdir(output_dir)
    except OSError:
        pass
    
    if emit_output:
        print "Running %s %s" % (ARTEMIS_EXEC, url)
    
    output = subprocess.check_output([ARTEMIS_EXEC, "-i 3", url], cwd=output_dir)

    if emit_output:
	print 'RESULT'
        print output

    fp = open(os.path.join(output_dir, 'stdout.txt'), 'w')
    fp.write(output)
    fp.close()

def assertTrue(value, msg=None):
    if not value:
        print '!!!!! ', msg, ' !!!!!'
        return False
    else:
        return True

def assertTrueFail(*args, **kwargs):
    if not assertTrue(*args, **kwargs):
        raise AssertFailure

def assert_file(output_dir, result_dir, filename):
    output = os.path.join(output_dir, filename)
    result = os.path.join(result_dir, filename)

    try:

        assertTrueFail(os.path.exists(output),
                       msg=u'Expected output file %s missing' % filename)

        assertTrueFail(os.path.exists(result),
                       msg=u'Expected reference file %s missing' % filename)

        equal = filecmp.cmp(output, result)

        assertTrue(equal, msg=u'NOT EQUAL: diff %s %s' % (output, result))

    except AssertFailure:
        pass

def test_fixutre(fixture_name):
    print '=== Testing fixture %s ===' % fixture

    execute_artemis(fixture_name)

    output_dir, result_dir, url = get_fixture_paths(fixture_name)

    assert_file(output_dir, result_dir, 'stdout.txt')

def update_fixture(fixture_name):
    execute_artemis(fixture_name)

    output_dir, result_dir, url = get_fixture_paths(fixture_name)

    shutil.rmtree(result_dir, ignore_errors=True)
    shutil.copytree(output_dir, result_dir)

def run_fixture(fixture_name):
    execute_artemis(fixture_name, emit_output=True)

def fixture_discovery():
    fixture_dir = os.path.join(THIS_DIR, 'fixtures')

    return os.listdir(fixture_dir)

commands = {'run': run_fixture,
            'test': test_fixutre,
            'update': update_fixture}

if __name__ == '__main__':

    if len(sys.argv) == 1 or (sys.argv[1] not in commands.keys()):
        print 'usage: python %s test|update|run [fixture]' % sys.argv[0]
        sys.exit(1)

    if len(sys.argv) > 2:
        fixtures = [sys.argv[2]]
    else:
        fixtures = fixture_discovery()

    try:
        command = commands[sys.argv[1]]
    except KeyError:
        print 'Unknown command'
        sys.exit(1)

    setup_testing_env()

    try:
        for fixture in fixtures:
            command(fixture)

    finally:
        teardown_testing_env()
        sys.exit(0)
