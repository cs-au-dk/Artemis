#!/usr/bin/env python

"""
Test suite for Artemis Analysis-Server mode.
"""

import os
import unittest
import subprocess
import json
import time

FIXTURE_ROOT = os.path.join(os.environ['ARTEMISDIR'], 'artemis-code', 'tests', 'system', 'fixtures', 'server')

ARTEMIS_EXEC = 'artemis'
OUTPUT_DIR = '.output'

ARTEMIS_SERVER_PORT = 8008
ARTEMIS_SERVER_URL = 'http://localhost:%s' % ARTEMIS_SERVER_PORT



class Concolic(unittest.TestCase):
    
    def setUp(self):
        # Run the server and save a reference so we can kill it in the end.
        self.server = run_artemis_server()
    
    def tearDown(self):
        # End the server.
        self.server.terminate()
        self.server.wait()
        assert(self.server.poll() is not None)
    
    def test_server_process_is_running(self):
        self.assertTrue(self.server.poll() is None)
    
    @unittest.skip("Not yet implemented")
    def test_connect_to_server(self):
        self.fail("Not implemented")
    
    @unittest.skip("Not yet implemented")
    def test_echo_command(self):
        self.fail("Not implemented")
    
    @unittest.skip("Not yet implemented")
    def test_server_busy(self):
        self.fail("Not implemented")
    
    @unittest.skip("Not yet implemented")
    def test_invalid_request(self):
        self.fail("Not implemented")
    
    @unittest.skip("Not yet implemented")
    def test_pageload_command(self):
        self.fail("Not implemented")
    
    @unittest.skip("Not yet implemented")
    def test_exit_command(self):
        self.fail("Not implemented")
    


def fixture_url(page):
    """Returns the (local) URL for a given test page."""
    return os.path.join(FIXTURE_ROOT, page)


def run_artemis_server():
    """
    Runs Artemis in server mode and returns the PID which can be used to check on it or kill it.
    
    We can't use the harness.execute_artemis() method, as it waits until the run is finished and returns its results.
    """
    
    cmd = [ARTEMIS_EXEC] + ["--major-mode", "server", "--analysis-server-port", str(ARTEMIS_SERVER_PORT)]
    
    p = subprocess.Popen(cmd, cwd=OUTPUT_DIR, stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    
    # Hack to give the server a little time to come up.
    time.sleep(1)
    
    return p


def send_to_server_string(message):
    """Sends a command to the running server and returns the result."""
    pass

def send_to_server(message):
    """JSON enoding/decoding wrapper for send_to_server()."""
    pass


if __name__ == '__main__':
    unittest.main(buffer=True)
