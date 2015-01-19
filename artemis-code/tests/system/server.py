#!/usr/bin/env python

"""
Test suite for Artemis Analysis-Server mode.
"""

import os
import unittest
import subprocess
import urllib2
import json
import time
import httplib

FIXTURE_ROOT = os.path.join(os.environ['ARTEMISDIR'], 'artemis-code', 'tests', 'system', 'fixtures', 'server')

ARTEMIS_EXEC = 'artemis'
OUTPUT_DIR = '.output'

ARTEMIS_SERVER_PORT = 8008
ARTEMIS_SERVER_URL = 'http://localhost:%s' % ARTEMIS_SERVER_PORT



class Concolic(unittest.TestCase):
    
    def setUp(self):
        # Run the server and save a reference so we can kill it in the end.
        self.server = run_artemis_server()
        self.expectedTerminated = False
    
    def tearDown(self):
        # End the server.
        try:
            self.server.terminate()
            self.server.wait()
            assert(self.server.poll() is not None)
        except OSError:
            if not self.expectedTerminated:
                raise
    
    def test_server_process_is_running(self):
        self.assertTrue(self.server.poll() is None)
    
    def test_connect_to_server(self):
        # Just check we can open the URL without an exception
        urllib2.urlopen(ARTEMIS_SERVER_URL)
    
    def test_echo_command(self):
        message = {
                "command": "echo",
                "message": "Hello, World!"
            }
        
        response = send_to_server(message)
        
        self.assertIn("message", response)
        self.assertEqual(response["message"], u"Hello, World!")
    
    def test_empty_request(self):
        message = ""
        
        response = send_to_server(message, False)
        
        self.assertIn("error", response)
    
    def test_invalid_json(self):
        message = "{ This is ]] not :, valid { JSON !"
        
        response = send_to_server(message, False)
        
        self.assertIn("error", response)
    
    def test_invalid_request(self):
        message = {
                "required": "fields are not",
                "present": "in this example"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_exit_command(self):
        message = {
                "command": "exit"
            }
        
        try:
            response = send_to_server(message)
        except httplib.BadStatusLine:
            pass
        
        time.sleep(0.5)
        
        self.assertIsNot(self.server.poll(), None)
        
        # Stop an exception being thrown by tearDown().
        self.expectedTerminated = True
    
    @unittest.skip("Not yet implemented")
    def test_server_busy(self):
        self.fail("Not implemented")
    
    @unittest.skip("Not yet implemented")
    def test_pageload_command(self):
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
    time.sleep(0.5)
    
    return p


def send_to_server(message, encode_json=True):
    """Sends a command to the running server and returns the result."""
    
    if encode_json:
        data = json.dumps(message)
    else:
        data = str(message)
    
    response = urllib2.urlopen(ARTEMIS_SERVER_URL, data)
    
    return json.load(response)


if __name__ == '__main__':
    unittest.main(buffer=True)
