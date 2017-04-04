#!/usr/bin/env python

"""
Test suite for Artemis Analysis-Server mode.
"""

import os
import sys
import unittest
import subprocess
import urllib2
import json
import time
import httplib
import socket
import re
import shutil
import contextlib

from harness.web_server_for_edge_case_testing import BackgroundTestServer
from harness.web_server_for_edge_case_testing import HOST_NAME as TEST_SERVER_HOST
from harness.web_server_for_edge_case_testing import PORT as TEST_SERVER_PORT

FIXTURE_ROOT = os.path.join(os.environ['ARTEMISDIR'], 'artemis-code', 'tests', 'system', 'fixtures', 'server')

ARTEMIS_EXEC = 'artemis'
OUTPUT_DIR = '.output'

ARTEMIS_SERVER_PORT = 8008
ARTEMIS_SERVER_URL = 'http://localhost:%s' % ARTEMIS_SERVER_PORT

DEBUG_SHOW_ARTEMIS_OUTPUT = False


class AnalysisServerTestBase(unittest.TestCase):
    
    def setUp(self):
        # Run the server and save a reference so we can kill it in the end.
        self.server = run_artemis_server(self.name())
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
    
    def name(self):
        return self.id().split(".")[-1]
    
    def get_server_log(self, test_name):
        log_file = os.path.join(OUTPUT_DIR, test_name, "server-log.txt")
        if not os.path.isfile(log_file):
            return None
        with open(log_file) as f:
            lines = f.readlines()
        def strip_variable_info(x):
            x = re.sub("^\[[- \d]+\] ", "", x.rstrip())
            x = re.sub("^(    Build (.*?):)(.*)$", "\\1 XXX", x)
            x = re.sub("^(    Called: )(.*/)?(artemis (.*))$", "\\1\\3", x) # Makes the test more robust under different settings of ARTEMIS_EXEC which some versions of this script use.
            return x
        return [strip_variable_info(x) for x in lines]
    
    def get_graph(self, test_name, tree_number=1):
        graph_file = os.path.join(OUTPUT_DIR, test_name, "server-tree-" + str(tree_number) + ".gv")
        
        if not os.path.isfile(graph_file):
            return None
        
        with open(graph_file) as f:
            full_graph = f.readlines()
        
        # Filter out only the interesting part of the graph
        result = [re.sub(" \[.*\]", "", edge.strip()) for edge in full_graph if "->" in edge]
        return result
    
    def assertServerAcceptingConnections(self):
        try:
            # Just check we can open the URL without an exception
            urllib2.urlopen(ARTEMIS_SERVER_URL)
        except:
            self.fail("Connecting to the server raised " + sys.exc_info()[0].__name__)
    
    def assertStatusElementContains(self, expected_status):
        """Use the 'element' command to check the page state reported by the test fixture."""
        
        check_message = {
            "command": "element",
            "element": "id('status')"
        }
        
        check_response = send_to_server(check_message)
        
        self.assertIn("elements", check_response)
        self.assertEqual(check_response["elements"], [u"<span id=\"status\">%s</span>" % expected_status])
    
    def loadPage(self, page):
        message = {
                "command": "pageload",
                "url": page
            }
        
        response = send_to_server(message)
        
        self.assertIn("pageload", response)
        self.assertEqual(response["pageload"], u"done")
        self.assertNotIn("error", response)
    
    def loadFixture(self, fixture):
        self.loadPage(fixture_url(fixture))
    
    def formInput(self, field, value):
        message = {
                "command": "forminput",
                "field": field,
                "value": value
            }
        
        response = send_to_server(message)
        self.assertNotIn("error", response)
        self.assertIn("forminput", response)
    
    def click(self, element):
        message = {
                "command": "click",
                "element": element
            }
        
        response = send_to_server(message)
        self.assertNotIn("error", response)
        self.assertIn("click", response)
    
    def assertUrl(self, url):
        page_message = {
            "command": "page"
        }
        
        page_response = send_to_server(page_message)
        
        self.assertNotIn("error", page_response)
        self.assertIn("url", page_response)
        self.assertEqual(page_response["url"], url)
    

class AnalysisServerFeatureTests(AnalysisServerTestBase):
    
    def test_server_process_is_running(self):
        self.assertTrue(self.server.poll() is None)
    
    def test_connect_to_server(self):
        self.assertServerAcceptingConnections()
    
    def test_port_check(self):
        # Run  an extra server and confirm it terminates with an error.
        
        second_server = run_artemis_server(self.name() + "_extra")
        time.sleep(1)
        ret = second_server.poll()
        if ret is None:
            second_server.terminate()
            second_server.wait()
        if ret != 1:
            self.fail("Two servers runnig on the same port did not give an error.")
    
    def test_echo_command(self):
        message = {
                "command": "echo",
                "message": "Hello, World!"
            }
        
        response = send_to_server(message)
        
        self.assertIn("message", response)
        self.assertEqual(response["message"], u"Hello, World!")
    
    def test_server_log(self):
        message = {
                "command": "echo",
                "message": "Hello, World!"
            }
        
        response = send_to_server(message)
        
        self.assertNotIn("error", response)
        
        log = self.get_server_log(self.name())
        self.assertIsNotNone(log)
        
        expected_log = """
Server started.
    Build date: XXX
    Build commit: XXX
    Called: artemis --major-mode server --analysis-server-port 8008 -v all --analysis-server-log
Received:
    {"message": "Hello, World!", "command": "echo"}
Sent:
    { "message" : "Hello, World!" }
"""
        expected_log = expected_log.split("\n")[1:-1]
        
        self.assertEqual(log, expected_log)
    
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
    
    def test_unexpected_field(self):
        message = {
                "command": "echo",
                "message": "Hello, World!",
                "fake-option": "some value"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_response_headers(self):
        message = {
                "command": "echo",
                "message": "Hello, World!"
            }
        
        response = send_to_server(message, return_urllib_response=True)
        
        self.assertEqual(response.info().gettype(), "application/json")
    
    def test_exit_command(self):
        message = {
                "command": "exit"
            }
        
        response = send_to_server(message)
        
        self.assertIn("message", response)
        
        time.sleep(2) # Server waits 1s while shutting down to finish sending the final message.
        
        self.assertIsNot(self.server.poll(), None)
        
        # Stop an exception being thrown by tearDown().
        self.expectedTerminated = True
    
    def test_broken_connection(self):
        slow_message = {
                "command": "echo",
                "message": "I am a slow command.",
                "delay": 1
            }
        
        # Send the slow command but time-out before it finishes.
        try:
            slow_response = send_to_server(slow_message, timeout=0.5)
        except socket.timeout:
            pass
        
        # Check the server is still up and accepting connections.
        urllib2.urlopen(ARTEMIS_SERVER_URL)
    
    def test_server_busy(self):
        slow_message = {
                "command": "echo",
                "message": "I am a slow command.",
                "delay": 1
            }
        
        # Send the slow command but time-out before it finishes.
        try:
            slow_response = send_to_server(slow_message, timeout=0.5)
        except socket.timeout:
            pass
        
        # Send another command before the first has finished.
        busy_message = {
                "command": "echo",
                "message": "The server will be busy."
            }
        
        busy_response = send_to_server(busy_message)
        
        self.assertIn("error", busy_response)
        
        # Wait for the first to finish and confirm everything is working OK again.
        time.sleep(1)
        
        ok_message = {
                "command": "echo",
                "message": "The server will be OK now."
            }
        
        ok_response = send_to_server(ok_message)
        
        self.assertNotIn("error", ok_response)
        self.assertIn("message", ok_response)
    
    def test_pageload_command(self):
        message = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        response = send_to_server(message)
        
        self.assertIn("pageload", response)
        self.assertEqual(response["pageload"], u"done")
        
        self.assertIn("url", response)
        self.assertEqual(response["url"], fixture_url_with_scheme("handlers.html"))
    
    def test_pageload_command_https(self):
        message = {
                "command": "pageload",
                "url": "https://www.example.com"
            }
        
        response = send_to_server(message)
        
        self.assertIn("pageload", response)
        self.assertEqual(response["pageload"], u"done")
        
        self.assertIn("url", response)
        self.assertEqual(response["url"], u"https://www.example.com/")
    
    def test_pageload_bad_url(self):
        message = {
                "command": "pageload",
                "url": fixture_url("this-page-doesnt-exist.html")
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_pageload_bad_url_after_good(self):
        good_message = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        good_response = send_to_server(good_message)
        
        self.assertNotIn("error", good_response)
        self.assertIn("pageload", good_response)
        
        bad_message = {
                "command": "pageload",
                "url": fixture_url("this-page-doesnt-exist.html")
            }
        
        bad_response = send_to_server(bad_message)
        
        self.assertIn("error", bad_response)
        self.assertNotIn("pageload", bad_response)
        self.assertNotIn("pageload", bad_response)
    
    def test_pageload_command_redirect_301(self):
        message = {
                "command": "pageload",
                "url": "http://bit.ly/1h0ceQI"
            }
        
        response = send_to_server(message)
        
        self.assertIn("url", response)
        self.assertEqual(response["url"], u"http://www.example.com/")
    
    def test_pageload_command_redirect_301_to_https(self):
        message = {
                "command": "pageload",
                "url": "http://bit.ly/1gG5wiT"
            }
        
        response = send_to_server(message)
        
        self.assertIn("url", response)
        self.assertEqual(response["url"], u"https://www.example.com/")
    
    def test_pageload_command_redirect_meta(self):
        message = {
                "command": "pageload",
                "url": fixture_url("redirect-meta.html")
            }
        
        response = send_to_server(message)
        
        self.assertIn("url", response)
        self.assertEqual(response["url"], fixture_url_with_scheme("handlers.html"))
    
    def test_pageload_command_redirect_meta_single_hop_only(self):
        """
        The meta-redirect detection only waits for a single redirection. If there is more than one level of redirect,
        this is not supported. This is to avoid getting stuck in a redirect loop.
        """
        
        message = {
                "command": "pageload",
                "url": fixture_url("redirect-meta-double.html")
            }
        
        response = send_to_server(message)
        
        self.assertIn("url", response)
        self.assertEqual(response["url"], fixture_url_with_scheme("redirect-meta.html"))
    
    def test_pageload_command_redirect_js_not_supported(self):
        """
        We cannot detect when a page redirection is done via JavaScript, so the pageload command does not wait.
        See issue #116.
        """
        
        message = {
                "command": "pageload",
                "url": fixture_url("redirect-js.html")
            }
        
        response = send_to_server(message)
        
        self.assertIn("url", response)
        self.assertEqual(response["url"], fixture_url_with_scheme("redirect-js.html"))
    
    def test_pageload_command_redirect_js_2_not_supported(self):
        """
        We cannot detect when a page redirection is done via JavaScript, so the pageload command does not wait.
        See issue #116.
        """
        
        message = {
                "command": "pageload",
                "url": fixture_url("redirect-js-2.html")
            }
        
        response = send_to_server(message)
        
        self.assertIn("url", response)
        self.assertEqual(response["url"], fixture_url_with_scheme("redirect-js-2.html"))
    
    
    def test_pageload_command_redirect_meta_no_crash(self):
        message = {
                "command": "pageload",
                "url": fixture_url("redirect-meta.html")
            }
        
        response = send_to_server(message)
        
        # Wait for the redirect and check the server is up.
        time.sleep(1.5)
        self.assertServerAcceptingConnections()
    
    def test_pageload_command_redirect_js_no_crash(self):
        message = {
                "command": "pageload",
                "url": fixture_url("redirect-js.html")
            }
        
        response = send_to_server(message)
        
        # Wait for the redirect and check the server is up.
        time.sleep(1.5)
        self.assertServerAcceptingConnections()
        
    def test_pageload_command_redirect_js_2_no_crash(self):
        message = {
                "command": "pageload",
                "url": fixture_url("redirect-js-2.html")
            }
        
        response = send_to_server(message)
        
        # Wait for the redirect and check the server is up.
        time.sleep(1.5)
        self.assertServerAcceptingConnections()
    
    def test_pageload_command_timeout(self):
        message = {
                "command": "pageload",
                "url": "http://www.mistymountain.co.uk/", # Any non-trivial page will do.
                "timeout": 10
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
        self.assertEqual(response["error"], u"Timed out.")
    
    def test_pageload_command_timeout_not_triggered(self):
        message = {
                "command": "pageload",
                "url": "http://www.mistymountain.co.uk/", # As before, but with a longer timeout.
                "timeout": 20000
            }
        
        response = send_to_server(message)
        
        self.assertNotIn("error", response)
        self.assertIn("pageload", response)
        self.assertEqual(response["pageload"], u"done")
    
    @unittest.expectedFailure #See issue #117
    def test_pageload_command_timeout_blocking_js(self):
        message = {
                "command": "pageload",
                "url": fixture_url("slow-load.html"),
                "timeout": 500
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
        self.assertEqual(response["error"], u"Timed out.")
    
    def test_handlers_command(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        load_response = send_to_server(load_message)
        # load_response is already tested by test_pageload_command()
        
        message = {
            "command": "handlers"
        }
        
        response = send_to_server(message)
        
        self.assertIn("handlers", response)
        
        handlers = response["handlers"]
        
        self.assertEqual(len(handlers), 3)
        
        expected_handlers = json.loads("""
            [
                {
                    "element": "//a[@id='dom-attr']",
                    "events": ["click"]
                },
                {
                    "element": "//a[@id='js-attr']",
                    "events": ["click"]
                },
                {
                    "element": "//a[@id='listener']",
                    "events": ["click", "focus"]
                }
            ]
        """)
        
        self.assertEqual(handlers, expected_handlers)
        
    def test_handlers_command_xpath_corner_cases(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("handlers-xpath-corner-cases.html")
            }
        
        load_response = send_to_server(load_message)
        # load_response is already tested by test_pageload_command()
        
        message = {
            "command": "handlers"
        }
        
        response = send_to_server(message)
        
        self.assertIn("handlers", response)
        
        handlers = response["handlers"]
        
        self.assertEqual(len(handlers), 3)
        
        expected_handlers = json.loads("""
            [
                {
                    "element": "/html/body[1]",
                    "events": ["click"]
                },
                {
                    "element": "document",
                    "events": ["click"]
                },
                {
                    "element": "window",
                    "events": ["click"]
                }
            ]
        """)
        
        self.assertEqual(handlers, expected_handlers)
        
    
    def test_handlers_command_with_filter(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        message = {
            "command": "handlers",
            "filter": "id('listener')"
        }
        
        response = send_to_server(message)
        
        self.assertIn("handlers", response)
        
        handlers = response["handlers"]
        
        self.assertEqual(len(handlers), 1)
        
        expected_handlers = json.loads("""
            [
                {
                    "element": "//a[@id='listener']",
                    "events": ["click", "focus"]
                }
            ]
        """)
        
        self.assertEqual(handlers, expected_handlers)
    
    def test_handlers_command_without_load(self):
        message = {
            "command": "handlers"
        }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_click_command(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        click_message = {
                "command": "click",
                "element": "id(\"clickable\")"
            }
        
        click_response = send_to_server(click_message)
        
        self.assertIn("click", click_response)
        self.assertEqual(click_response["click"], u"done")
    
    def test_click_command_without_load(self):
        message = {
                "command": "click",
                "element": "id(\"clickable\")"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_click_command_with_invalid_xpath(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        click_message = {
                "command": "click",
                "element": "this is not a real xpath"
            }
        
        click_response = send_to_server(click_message)
        
        self.assertIn("error", click_response)
    
    def test_click_command_with_no_element(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        click_message = {
                "command": "click",
                "element": "id(\"no-such-element-exists\")"
            }
        
        click_response = send_to_server(click_message)
        
        self.assertIn("error", click_response)
    
    def test_click_command_with_handlers_check(self):
        # Uses the handlers command to confirm the click actually worked.
        
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        handlers_message = {
                "command": "handlers"
            }
        
        handlers_initial_response = send_to_server(handlers_message)
        
        self.assertIn("handlers", handlers_initial_response)
        self.assertEqual(len(handlers_initial_response["handlers"]), 1)
        
        click_message = {
                "command": "click",
                "element": "id(\"clickable\")"
            }
        
        click_response = send_to_server(click_message)
        
        self.assertIn("click", click_response)
        self.assertEqual(click_response["click"], u"done")
        
        handlers_final_response = send_to_server(handlers_message)
        
        self.assertIn("handlers", handlers_final_response)
        self.assertEqual(len(handlers_final_response["handlers"]), 2)
    
    def test_click_command_method_simple(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click-mouse-events.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        click_message = {
            "command": "click",
            "element": "id('button')",
            "method": "simple"
        }
        
        click_response = send_to_server(click_message)
        
        self.assertIn("click", click_response)
        self.assertNotIn("error", click_response)
        
        self.assertStatusElementContains("click ")
    
    def test_click_command_method_simulate_js(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click-mouse-events.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        click_message = {
            "command": "click",
            "element": "id('button')",
            "method": "simulate-js"
        }
        
        click_response = send_to_server(click_message)
        
        self.assertIn("click", click_response)
        self.assertNotIn("error", click_response)
        
        self.assertStatusElementContains("mouseover mousemove mousedown focus mouseup click mousemove mouseout blur ")
    
    def test_click_command_method_simulate_gui(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click-mouse-events.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        click_message = {
            "command": "click",
            "element": "id('button')",
            "method": "simulate-gui"
        }
        
        click_response = send_to_server(click_message)
        
        self.assertIn("click", click_response)
        self.assertNotIn("error", click_response)
        
        self.assertStatusElementContains("mouseover mousedown focus mouseup click ")
    
    def test_click_command_method_simulate_gui_with_auto_scroll_required(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click-mouse-events.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        click_message = {
            "command": "click",
            "element": "id('button-below-fold')",
            "method": "simulate-gui"
        }
        
        click_response = send_to_server(click_message)
        
        self.assertIn("click", click_response)
        self.assertNotIn("error", click_response)
        
        self.assertStatusElementContains("below-fold-click ")
    
    def test_click_command_method_simulate_gui_after_page_scroll(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click-after-scroll.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        click_message = {
            "command": "click",
            "element": "id('click-btn')",
            "method": "simulate-gui"
        }
        scroll_message = {
            "command": "click",
            "element": "id('scroll-btn')",
            "method": "simulate-gui"
        }
        
        response = send_to_server(click_message)
        self.assertIn("click", response)
        self.assertNotIn("error", response)
        
        response = send_to_server(scroll_message)
        self.assertIn("click", response)
        self.assertNotIn("error", response)
        
        response = send_to_server(click_message)
        self.assertIn("click", response)
        self.assertNotIn("error", response)
        
        
        self.assertStatusElementContains("Clicked Scrolled Clicked ")
    
    def test_dom_command_deprecated(self):
        message = {
            "command": "dom"
        }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_page_command(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        # Send the page command
        page_message = {
            "command": "page"
        }
        
        page_response = send_to_server(page_message)
        
        # Read the expected DOM from the HTML file directly.
        with open(fixture_url("handlers.html")) as f:
            expected_dom = unicode(f.read())
        
        # This is a hack to avoid parsing the page. http://stackoverflow.com/a/1732454/1044484
        expected_dom_elts = len(re.findall("<[^/!]", expected_dom))
        expected_dom_chars = len(expected_dom.strip())
        
        # Element count does not include the html element itself.
        elt_adjustment = 1
        # Char count is different because whitespace is removed from the end of elements in our webkit. <a href="" > becomes <a href="">
        char_adjustment = len(re.findall("\" >", expected_dom))
        
        self.assertIn("url", page_response)
        self.assertEqual(page_response["url"], fixture_url_with_scheme("handlers.html"))
        
        self.assertIn("title", page_response)
        self.assertEqual(page_response["title"], "Ben Spencer")
        
        self.assertIn("elements", page_response)
        self.assertEqual(page_response["elements"], expected_dom_elts - elt_adjustment)
        
        self.assertIn("characters", page_response)
        self.assertEqual(page_response["characters"], expected_dom_chars - char_adjustment)
    
    def test_page_command_without_load(self):
        message = {
                "command": "page"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_page_command_with_dom(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        # Send the page command
        page_message = {
            "command": "page",
            "dom": True
        }
        
        page_response = send_to_server(page_message)
        
        self.assertIn("dom", page_response)
        
        # Read the expected DOM from the HTML file directly.
        with open(fixture_url("handlers.html")) as f:
            expected = unicode(f.read())
        
        # Ignore whitespace differences.
        # Artemis IDs are not being added, so we don't have to account for these with a "proper" diff.
        exp_tokens = [x for x in re.split("\s+|<|>", expected) if x != ""]
        real_tokens = [x for x in re.split("\s+|<|>", page_response["dom"]) if x != ""]
        
        self.assertEqual(real_tokens, exp_tokens)
        
        # Check everything else was at least still in the response as well.
        self.assertIn("url", page_response)
        self.assertIn("title", page_response)
        self.assertIn("elements", page_response)
        self.assertIn("characters", page_response)
    
    def test_page_command_with_invalid_dom_request(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        # Send the page command
        page_message = {
            "command": "page",
            "dom": "Yes please!"
        }
        
        page_response = send_to_server(page_message)
        
        self.assertIn("error", page_response)
    
    def test_element_command(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        element_message = {
                "command": "element",
                "element": "id(\"clickable\")"
            }
        
        element_response = send_to_server(element_message)
        
        self.assertIn("elements", element_response)
        self.assertEqual(element_response["elements"], [u"<a href=\"\" id=\"clickable\">Click here to add new buttons to the page.</a>"])
    
    def test_element_command_with_invalid_xpath(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        element_message = {
                "command": "element",
                "element": "this is not a real xpath"
            }
        
        element_response = send_to_server(element_message)
        
        self.assertIn("error", element_response)
    
    def test_element_command_with_no_element(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        element_message = {
                "command": "element",
                "element": "id(\"no-such-element-exists\")"
            }
        
        element_response = send_to_server(element_message)
        
        self.assertIn("elements", element_response)
        self.assertEqual(element_response["elements"], [])
    
    def test_element_command_multiple(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        element_message = {
                "command": "element",
                "element": "//hr"
            }
        
        element_response = send_to_server(element_message)
        
        self.assertIn("elements", element_response)
        self.assertEqual(element_response["elements"], [u"<hr>", u"<hr>"])
    
    def test_element_command_without_load(self):
        message = {
                "command": "element",
                "element": ""
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_element_command_with_property(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        element_message = {
                "command": "element",
                "element": "id(\"clickable\")",
                "property": "nodeName"
            }
        
        element_response = send_to_server(element_message)
        
        self.assertIn("elements", element_response)
        self.assertEqual(element_response["elements"], [u"A"])
    
    def test_fieldsread_command(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        fieldsread_message = {
            "command": "fieldsread"
        }
        
        fieldsread_response = send_to_server(fieldsread_message)
        
        self.assertIn("fieldsread", fieldsread_response)
        self.assertEqual(fieldsread_response["fieldsread"], [])
    
    def test_fieldsread_command_with_clicks(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        # Send a few click commands
        def click_btn_message(btn_num):
            return {
                    "command": "click",
                    "element": ("//button[%s]" % btn_num)
                }
        
        r = send_to_server(click_btn_message(1))
        self.assertNotIn("error", r)
        r = send_to_server(click_btn_message(1))
        self.assertNotIn("error", r)
        r = send_to_server(click_btn_message(2))
        self.assertNotIn("error", r)
        r = send_to_server(click_btn_message(3))
        self.assertNotIn("error", r)
        r = send_to_server(click_btn_message(3))
        self.assertNotIn("error", r)
        r = send_to_server(click_btn_message(3))
        self.assertNotIn("error", r)
        
        # Send the fieldsread command
        fieldsread_message = {
            "command": "fieldsread"
        }
        
        fieldsread_response = send_to_server(fieldsread_message)
        
        expected = json.loads("""
            {
                "fieldsread": [
                    {
                        "element": "/html/body[1]/form[1]/button[1]",
                        "event": "click/simple",
                        "reads": [
                            {
                                "count": 2,
                                "field": "//input[@id='first']"
                            }
                        ]
                    },
                    {
                        "element": "/html/body[1]/form[1]/button[2]",
                        "event": "click/simple",
                        "reads": [
                            {
                                "count": 1,
                                "field": "//input[@id='second']"
                            }
                        ]
                    },
                    {
                        "element": "/html/body[1]/form[1]/button[3]",
                        "event": "click/simple",
                        "reads": [
                            {
                                "count": 3,
                                "field": "//input[@id='first']"
                            },
                            {
                                "count": 3,
                                "field": "//input[@id='second']"
                            }
                        ]
                    }
                ]
            }
        """)
        
        self.assertEqual(fieldsread_response, expected)
    
    def test_fieldsread_command_with_various_events(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_messages = [
                {
                    "command": "click",
                    "element": "//button[1]",
                    "method": "simple"
                },
                {
                    "command": "click",
                    "element": "//button[1]",
                    "method": "simulate-js"
                },
                {
                    "command": "event",
                    "element": "//button[1]",
                    "event": "click"
                },
                {
                    "command": "event",
                    "element": "//input[1]",
                    "event": "change"
                },
                {
                    "command": "forminput",
                    "field": "//input[1]",
                    "value": "Test",
                    "method": "onchange"
                },
                {
                    "command": "forminput",
                    "field": "//input[1]",
                    "value": "Test",
                    "method": "simulate-js"
                }
            ]
        
        for evt_message in event_messages:
            r = send_to_server(evt_message)
            self.assertNotIn("error", r)
        
        # Send the fieldsread command
        fieldsread_message = {
            "command": "fieldsread"
        }
        
        fieldsread_response = send_to_server(fieldsread_message)
        
        expected = json.loads("""
            {
                "fieldsread": [
                    {
                        "element": "/html/body[1]/form[1]/button[1]",
                        "event": "click/simple",
                        "reads": [
                            {
                                "count": 1,
                                "field": "//input[@id='first']"
                            }
                        ]
                    },
                    {
                        "element": "/html/body[1]/form[1]/button[1]",
                        "event": "click/simulate-js",
                        "reads": [
                            {
                                "count": 1,
                                "field": "//input[@id='first']"
                            }
                        ]
                    },
                    {
                        "element": "//input[@id='first']",
                        "event": "event/change",
                        "reads": [
                            {
                                "count": 1,
                                "field": "//input[@id='first']"
                            }
                        ]
                    },
                    {
                        "element": "/html/body[1]/form[1]/button[1]",
                        "event": "event/click",
                        "reads": [
                            {
                                "count": 1,
                                "field": "//input[@id='first']"
                            }
                        ]
                    },
                    {
                        "element": "//input[@id='first']",
                        "event": "forminput/onchange",
                        "reads": [
                            {
                                "count": 1,
                                "field": "//input[@id='first']"
                            }
                        ]
                    },
                    {
                        "element": "//input[@id='first']",
                        "event": "forminput/simulate-js",
                        "reads": [
                            {
                                "count": 1,
                                "field": "//input[@id='first']"
                            }
                        ]
                    }
                ]
            }
        """)
        
        self.assertEqual(fieldsread_response, expected)
    
    def test_fieldsread_command_without_load(self):
        message = {
                "command": "fieldsread"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_backbutton_command(self):
        load_message_1 = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        load_message_2 = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        back_message = {
                "command": "backbutton"
            }
        
        response_1 = send_to_server(load_message_1)
        self.assertNotIn("error", response_1)
        
        response_2 = send_to_server(load_message_2)
        self.assertNotIn("error", response_2)
        
        back_response = send_to_server(back_message)
        
        self.assertNotIn("error", back_response)
        self.assertIn("backbutton", back_response)
        self.assertIn("url", back_response)
        self.assertEqual(back_response["url"], fixture_url_with_scheme("handlers.html"))
    
    def test_backbutton_command_without_load(self):
        message = {
                "command": "backbutton"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_backbutton_command_from_first_page(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("handlers.html")
            }
        
        back_message = {
                "command": "backbutton"
            }
        
        load_response = send_to_server(load_message)
        self.assertNotIn("error", load_response)
        
        back_response = send_to_server(back_message)
        
        self.assertIn("error", back_response)
    
    def test_forminput_command(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world."
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
    
    def test_forminput_command_without_load(self):
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world."
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
    
    def test_forminput_command_invalid_request(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
        
        forminput_message_2 = {
            "command": "forminput",
            "value": "Hello, world."
        }
        
        forminput_response_2 = send_to_server(forminput_message_2)
        
        self.assertIn("error", forminput_response_2)
    
    def test_forminput_command_invalid_value_type(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": {"objects": "not", "allowed": "here"}
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
    
    def test_forminput_command_invalid_value_type_for_input_field(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        # It seems pointless to split these into tons of individual tests, so here goes...
        
        # 1. TEXT input cannot accept INT
        forminput_message_1 = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": 1234
        }
        
        forminput_response_1 = send_to_server(forminput_message_1)
        
        self.assertIn("error", forminput_response_1)
        
        # 2. TEXT input cannot accept BOOL
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": True
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
        
        # 3. CHECKBOX input cannot accept STRING
        forminput_message = {
            "command": "forminput",
            "field": "id('input-checkbox')",
            "value": "Hello"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
        
        # 4. CHECKBOX input cannot accept INT
        forminput_message = {
            "command": "forminput",
            "field": "id('input-checkbox')",
            "value": 1234
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
        
        # 5. RADIO input cannot accept STRING
        forminput_message = {
            "command": "forminput",
            "field": "id('input-radio')",
            "value": "Hello"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
        
        # 6. RADIO input cannot accept INT
        forminput_message = {
            "command": "forminput",
            "field": "id('input-radio')",
            "value": 1234
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
        
        # 7. SELECT input cannot accept BOOL
        forminput_message = {
            "command": "forminput",
            "field": "id('input-select')",
            "value": True
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
    
    def test_forminput_command_no_element(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('nonexistant-element')",
            "value": "Hello, world."
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
    
    def test_forminput_command_element_not_unique(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "//input",
            "value": "Hello, world."
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
    
    def test_forminput_command_field_not_input(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('status')",
            "value": "Hello, world."
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
    
    def test_forminput_command_checkbox(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-checkbox')",
            "value": True
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("#input-checkbox set to true")
        
    def test_forminput_command_radio_button(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-radio-1')",
            "value": True
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("#input-radio-1 set to true")
    
    def test_forminput_command_select_box(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-select')",
            "value": "third"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("#input-select set to 'third' (index 2)")
    
    def test_forminput_command_invalid_select_value(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-select')",
            "value": "my-made-up-value"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("#input-select set to '' (index -1)")
    
    def test_forminput_command_select_box_by_index(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-select')",
            "value": 2
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("#input-select set to 'third' (index 2)")
    
    def test_forminput_command_method_inject(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world.",
            "method": "inject"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("Nothing changed.")
    
    def test_forminput_command_method_onchange(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world.",
            "method": "onchange"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("#input-text set to 'Hello, world.'")
    
    def test_forminput_command_method_simulate_js(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world.",
            "method": "simulate-js"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("#input-text set to 'Hello, world.' (keys: 'H','e','l','l','o',',',' ','w','o','r','l','d','.')")
    
    def test_forminput_command_method_simulate_js_noblur(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world.",
            "method": "simulate-js",
            "noblur": True
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains("#input-text set to 'Hello, world.' (keys: 'H','e','l','l','o',',',' ','w','o','r','l','d','.') (in focus)")
    
    def test_forminput_command_method_simulate_js_key_events(self):
        """
        Check the key events are being simulated accurately enough.
        Currently checks shift key use, charCode vs. keyCode and upper/lower case codes.
        """
        
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-key-events.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello",
            "method": "simulate-js"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains(" keydown 16; keydown 72; keypress 72; keyup 72; keyup 16; keydown 69; keypress 101; keyup 69; keydown 76; keypress 108; keyup 76; keydown 76; keypress 108; keyup 76; keydown 79; keypress 111; keyup 79;")
    
    @unittest.skip("Not yet implemented.")
    def test_forminput_command_method_simulate_gui(self):
        pass # TODO
    
    def test_forminput_command_method_invalid(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world.",
            "method": "no-such-simulation-method"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("error", forminput_response)
    
    @unittest.expectedFailure # Not yet implemented
    def test_forminput_command_with_enter_simulate_js(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-submission.html")
            }
        
        load_response = send_to_server(load_message)
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello\r",
            "method": "simulate-js"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        # If the form submitted we should be at about:blank.
        self.assertUrl(u"about:blank")
    
    @unittest.expectedFailure # Not yet implemented
    def test_forminput_command_with_enter_simulate_js_key_events(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-key-events.html")
            }
        
        load_response = send_to_server(load_message)
        self.assertIn("pageload", load_response)
        
        forminput_message = {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "a\r",
            "method": "simulate-js"
        }
        
        forminput_response = send_to_server(forminput_message)
        
        self.assertIn("forminput", forminput_response)
        self.assertEqual(forminput_response["forminput"], u"done")
        
        self.assertStatusElementContains(" keydown 65; keypress 97; keyup 65; keydown 13; keypress 13; keyup 13;")
    
    @unittest.skip("Not yet implemented.")
    def test_forminput_command_with_enter_simulate_gui(self):
        pass # TODO
    
    def test_xpath_command_node_set(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        xpath_message = {
                "command": "xpath",
                "xpath": "//h1"
            }
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("result", xpath_response)
        self.assertEqual(xpath_response["result"], [ u"<h1>Clickable elements</h1>" ])
    
    def test_xpath_command_string(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        xpath_message = {
                "command": "xpath",
                "xpath": "string(//h1)"
            }
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("result", xpath_response)
        self.assertEqual(xpath_response["result"], u"Clickable elements")
    
    def test_xpath_command_number(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        xpath_message = {
                "command": "xpath",
                "xpath": "string-length(string(//h1))"
            }
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("result", xpath_response)
        self.assertEqual(xpath_response["result"], 18)
    
    def test_xpath_command_boolean(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        xpath_message = {
                "command": "xpath",
                "xpath": "string-length(string(//h1)) > 10"
            }
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("result", xpath_response)
        self.assertEqual(xpath_response["result"], True)
    
    def test_xpath_command_list(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        xpath_message = {
                "command": "xpath",
                "xpath": [
                    "//h1",
                    "string(//h1)",
                    "string-length(string(//h1))",
                    "string-length(string(//h1)) > 10"
                ]
            }
        
        expected = [
                [ u"<h1>Clickable elements</h1>" ],
                u"Clickable elements",
                18,
                True
            ]
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("result", xpath_response)
        self.assertEqual(xpath_response["result"], expected)
    
    def test_xpath_command_list_empty(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        xpath_message = {
                "command": "xpath",
                "xpath": []
            }
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("result", xpath_response)
        self.assertEqual(xpath_response["result"], [])
    
    def test_xpath_command_list_single(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        xpath_message = {
                "command": "xpath",
                "xpath": [ "//h1" ]
            }
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("result", xpath_response)
        self.assertEqual(xpath_response["result"], [ [ u"<h1>Clickable elements</h1>" ] ])
    
    def test_xpath_command_invalid_xpath(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        xpath_message = {
                "command": "xpath",
                "xpath": ""
            }
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("error", xpath_response)
    
    def test_xpath_command_without_load(self):
        xpath_message = {
                "command": "xpath",
                "xpath": "//h1"
            }
        
        xpath_response = send_to_server(xpath_message)
        
        self.assertIn("error", xpath_response)
    
    def test_event_command_with_click_event(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"clickable\")",
                "event": "click"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertIn("event", event_response)
        self.assertEqual(event_response["event"], u"done")
        
        # Use the handlers command to confirm the click worked.
        handlers_message = {
                "command": "handlers"
            }
        
        handlers_response = send_to_server(handlers_message)
        
        self.assertIn("handlers", handlers_response)
        self.assertEqual(len(handlers_response["handlers"]), 2)
    
    def test_event_command_with_change_event(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-injection.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"input-text\")",
                "event": "change"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertIn("event", event_response)
        self.assertEqual(event_response["event"], u"done")
        
        self.assertStatusElementContains("#input-text set to ''")
    
    def test_event_command_custom_press_enter(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-submission.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"input-text\")",
                "event": "ARTEMIS-press-enter"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertIn("event", event_response)
        self.assertEqual(event_response["event"], u"done")
        
        # Check we got to the result page.
        # TODO: Sometimes the server is crashed here, as with test_post_form_submission
        self.assertUrl(u"about:blank")
        
    
    def test_event_command_custom_bad_event(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("form-submission.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"input-text\")",
                "event": "ARTEMIS-does-not-exist"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertNotIn("event", event_response)
        self.assertIn("error", event_response)
    
    def test_event_command_without_required_fields(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"clickable\")"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertIn("error", event_response)
        
        event_message_2 = {
                "command": "event",
                "event": "click"
            }
        
        event_response_2 = send_to_server(event_message_2)
        
        self.assertIn("error", event_response_2)
    
    def test_event_command_without_load(self):
        event_message = {
                "command": "event",
                "element": "id(\"clickable\")",
                "event": "click"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertIn("error", event_response)
    
    def test_event_command_event_not_registered(self):
        # This should be a safe no-op, without any error.
        
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"clickable\")",
                "event": "focus"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertIn("event", event_response)
        self.assertEqual(event_response["event"], u"done")
    
    def test_event_command_no_such_element(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"nonexistent-element\")",
                "event": "click"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertIn("error", event_response)
    
    def test_event_command_nonexistent_event(self):
        # This is also a safe no-op.
        
        load_message = {
                "command": "pageload",
                "url": fixture_url("click.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"clickable\")",
                "event": "nonexistent-event"
            }
        
        event_response = send_to_server(event_message)
        
        self.assertIn("event", event_response)
        self.assertEqual(event_response["event"], u"done")
    
    def test_event_command_blocking_for_pageload(self):
        load_message = {
            "command": "pageload",
            "url": fixture_url("click-causes-load.html")
        }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"click-pageload\")",
                "event": "click"
            }
        
        start_time = time.time()
        
        event_response = send_to_server(event_message)
        
        end_time = time.time()
        
        self.assertIn("event", event_response)
        self.assertEqual(event_response["event"], u"done")
        
        # This click loads slow-load.html so we confirm this command was blocking by checking the elapsed time, which
        # will be just over 3s.
        self.assertGreater(end_time - start_time, 2)
    
    def test_event_command_blocking_for_XHR_async(self):
        load_message = {
            "command": "pageload",
            "url": fixture_url("click-causes-load.html")
        }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"click-xhr\")",
                "event": "click"
            }
        
        start_time = time.time()
        
        event_response = send_to_server(event_message)
        
        end_time = time.time()
        
        self.assertIn("event", event_response)
        self.assertEqual(event_response["event"], u"done")
        
        # This includes a 3s delay in the XHR onload handler. So we should see a 3s delay while the command blocks.
        self.assertGreater(end_time - start_time, 2)
        self.assertStatusElementContains("Done.")
    
    @unittest.expectedFailure # POST submission is currently broken.
    def test_event_command_blocking_for_form_submission(self):
        load_message = {
            "command": "pageload",
            "url": fixture_url("form-submission-slow.html")
        }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        event_message = {
                "command": "event",
                "element": "id(\"clickable\")",
                "event": "click"
            }
        
        start_time = time.time()
        
        event_response = send_to_server(event_message)
        
        end_time = time.time()
        
        self.assertIn("event", event_response)
        self.assertEqual(event_response["event"], u"done")
        
        # This click loads slow-load.html so we confirm this command was blocking by checking the elapsed time, which
        # will be just over 3s.
        self.assertGreater(end_time - start_time, 2)
    
    def test_windowsize_default(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("resize-window.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        self.assertStatusElementContains("1200x800")
    
    def test_windowsize_command(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("resize-window.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        windowsize_message = {
                "command": "windowsize",
                "width": 1024,
                "height": 768
            }
        
        windowsize_response = send_to_server(windowsize_message)
        
        self.assertIn("windowsize", windowsize_response)
        self.assertEqual(windowsize_response["windowsize"], u"done")
        
        self.assertStatusElementContains("1024x768")
    
    def test_windowsize_command_invalid_size(self):
        load_message = {
                "command": "pageload",
                "url": fixture_url("resize-window.html")
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        windowsize_message = {
                "command": "windowsize",
                "width": -100,
                "height": 100000
            }
        
        windowsize_response = send_to_server(windowsize_message)
        
        self.assertIn("error", windowsize_response)
    
    def test_timeouts_fired(self):
        load_message = {
            "command": "pageload",
            "url": fixture_url("timers.html")
        }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        time.sleep(1.5)
        
        self.assertStatusElementContains("Timers: timer-0-fired timer-1000-fired")
    
    @unittest.skip("No test implemented")
    def test_cookies_working(self):
        pass # TODO
    
    @unittest.skip("No test implemented")
    def test_cookies_cleared_on_pageload(self):
        pass # TODO
    
    def test_post_form_submission(self):
        load_message = {
                "command": "pageload",
                "url": "http://www.w3schools.com/php/demo_form_post.php"
            }
        
        load_response = send_to_server(load_message)
        
        self.assertIn("pageload", load_response)
        
        # Fill the fields
        fill_message_1 = {
                "command": "forminput",
                "field": "//input[1]",
                "value": "Test"
            }
        
        fill_message_2 = {
                "command": "forminput",
                "field": "//input[2]",
                "value": "test@example.com"
            }
        
        fill_response_1 = send_to_server(fill_message_1)
        self.assertNotIn("error", fill_response_1)
        
        fill_response_2 = send_to_server(fill_message_2)
        self.assertNotIn("error", fill_response_1)
        
        # Submit the form (POST)
        submit_message = {
                "command": "click",
                "element": "//input[@type='submit']"
            }
        
        submit_response = send_to_server(submit_message)
        self.assertNotIn("error", submit_response)
        
        time.sleep(1) # Click is not blocking on the submission. See: test_event_command_blocking_for_form_submission
        
        # Check it worked.
        check_message = {
                "command": "page",
                "dom": True
            }
        
        # TODO: There are stability problems with this test specifically.
        # The server is often crashed after the previous call. (See also test_event_command_custom_press_enter)
        check_response = send_to_server(check_message)
        
        self.assertNotIn("error", check_response)
        
        self.assertIn("url", check_response)
        self.assertEqual(check_response["url"], u"https://www.w3schools.com/php/welcome.php")
        
        self.assertIn("dom", check_response)
        self.assertEqual(check_response["dom"], u"""<!DOCTYPE html><html><head></head><body>

Welcome Test<br>
Your email address is: test@example.com

</body></html>""")
    
    def test_frame_support(self):
        # Frames are supported in Artemis, so there should be no crashes or errors.
        # The Artemis infrastructure inspects frames recursively so for example we can see handlers within a frame.
        # However, server-mode comands do not support frames, so far example the XPaths returned by the handlers
        # command are frame-local, and commands to click an element cannot reach an element inside a frame.
        
        self.loadFixture("iframe.html")
        
        handlers_command = {
                "command": "handlers"
            }
        
        handlers_response = send_to_server(handlers_command)
        
        expected_handlers = [
                {
                    "element": "/html/body[1]/form[1]/button[1]",
                    "events": [ "click" ]
                }
            ]
        
        self.assertIn("handlers", handlers_response)
        self.assertEqual(handlers_response["handlers"], expected_handlers)
        
        click_command = {
                "command": "click",
                "element": "/html/body[1]/form[1]/button[1]"
            }
        
        click_response = send_to_server(click_command)
        
        self.assertIn("error", click_response)
    
    def test_evaluate_js_command(self):
        self.loadFixture("empty.html")
        
        eval_message = {
                "command": "evaluatejs",
                "js": "document.getElementById('status').textContent = 'TESTING'"
            }
        
        eval_resonse = send_to_server(eval_message)
        
        self.assertNotIn("error", eval_resonse)
        self.assertIn("evaluatejs", eval_resonse)
        self.assertEqual(eval_resonse["evaluatejs"], u"done")
        
        self.assertStatusElementContains("TESTING")
    
    def test_set_symbolic_values_command(self):
        self.loadFixture("empty.html")
        
        # First check the default symbolic value.
        check_sym_values_message = {
                "command": "evaluatejs",
                "js": "document.getElementById('status').textContent = artemisInputString('mystr') + ' ' + artemisInputInteger('mynum') + ' ' + artemisInputBoolean('myflag');"
            }
        
        check_sym_values_resonse_1 = send_to_server(check_sym_values_message)
        self.assertNotIn("error", check_sym_values_resonse_1)
        
        self.assertStatusElementContains(" 0 false")
        
        # Now, do the injection
        inject_message = {
                "command": "setsymbolicvalues",
                "values": {
                    "mystr": "testme",
                    "mynum": 123,
                    "myflag": True
                }
            }
        
        inject_resonse = send_to_server(inject_message)
        
        self.assertNotIn("error", inject_resonse)
        self.assertIn("setsymbolicvalues", inject_resonse)
        self.assertEqual(inject_resonse["setsymbolicvalues"], u"done")
        
        # Finally, check the updated symbolic value can be read back
        check_sym_values_resonse_2 = send_to_server(check_sym_values_message)
        self.assertNotIn("error", check_sym_values_resonse_2)
        
        self.assertStatusElementContains("testme 123 true")
    
    def test_set_symbolic_values_command_reset(self):
        self.loadFixture("empty.html")
        
        # The initial injection
        inject_message_1 = {
                "command": "setsymbolicvalues",
                "values": {
                    "mystr": "testme",
                    "mynum": 123,
                    "myflag": True
                }
            }
        
        inject_resonse_1 = send_to_server(inject_message_1)
        self.assertNotIn("error", inject_resonse_1)
        
        # Now overwrite one of the values, with a reset of the whole internal symbolic value table.
        inject_message_2 = {
                "command": "setsymbolicvalues",
                "values": {
                    "mystr": "secondstring"
                },
                "reset": True
            }
        
        inject_resonse_2 = send_to_server(inject_message_2)
        self.assertNotIn("error", inject_resonse_2)
        
        # The old values are cleared.
        check_sym_values_message = {
                "command": "evaluatejs",
                "js": "document.getElementById('status').textContent = artemisInputString('mystr') + ' ' + artemisInputInteger('mynum') + ' ' + artemisInputBoolean('myflag');"
            }
        
        check_sym_values_resonse = send_to_server(check_sym_values_message)
        self.assertNotIn("error", check_sym_values_resonse)
        
        self.assertStatusElementContains("secondstring 0 false")
        
    
    def test_set_symbolic_values_command_no_reset(self):
        self.loadFixture("empty.html")
        
        # The initial injection
        inject_message_1 = {
                "command": "setsymbolicvalues",
                "values": {
                    "mystr": "testme",
                    "mynum": 123,
                    "myflag": True
                }
            }
        
        inject_resonse_1 = send_to_server(inject_message_1)
        self.assertNotIn("error", inject_resonse_1)
        
        # Now overwrite one of the values, leaving the existing values as-is.
        inject_message_2 = {
                "command": "setsymbolicvalues",
                "values": {
                    "mystr": "secondstring"
                }
                # "reset": False is the default.
            }
        
        inject_resonse_2 = send_to_server(inject_message_2)
        self.assertNotIn("error", inject_resonse_2)
        
        # The old values are not cleared.
        check_sym_values_message = {
                "command": "evaluatejs",
                "js": "document.getElementById('status').textContent = artemisInputString('mystr') + ' ' + artemisInputInteger('mynum') + ' ' + artemisInputBoolean('myflag');"
            }
        
        check_sym_values_resonse = send_to_server(check_sym_values_message)
        self.assertNotIn("error", check_sym_values_resonse)
        
        self.assertStatusElementContains("secondstring 123 true")
    
    def test_set_symbolic_values_command_empty(self):
        # Setting an empty mapping of values is useful to just use the reset parameter alone, cearing all symbolic values.
        self.loadFixture("empty.html")
        
        # The initial injection
        inject_message_1 = {
                "command": "setsymbolicvalues",
                "values": {
                    "mystr": "testme",
                    "mynum": 123,
                    "myflag": True
                }
            }
        
        inject_resonse_1 = send_to_server(inject_message_1)
        self.assertNotIn("error", inject_resonse_1)
        
        # Now clear all values.
        inject_message_2 = {
                "command": "setsymbolicvalues",
                "values": {},
                "reset": True
            }
        
        inject_resonse_2 = send_to_server(inject_message_2)
        self.assertNotIn("error", inject_resonse_2)
        
        # The old values are ALL cleared.
        check_sym_values_message = {
                "command": "evaluatejs",
                "js": "document.getElementById('status').textContent = artemisInputString('mystr') + ' ' + artemisInputInteger('mynum') + ' ' + artemisInputBoolean('myflag');"
            }
        
        check_sym_values_resonse = send_to_server(check_sym_values_message)
        self.assertNotIn("error", check_sym_values_resonse)
        
        self.assertStatusElementContains(" 0 false")
        


class AnalysisServerSystemTests(AnalysisServerTestBase):
    pass
    


class AnalysisServerConcolicAdviceTestBase(AnalysisServerTestBase):
    def concolicBeginTrace(self, identifier, implicitendtrace=None):
        message = {
                "command": "concolicadvice",
                "action": "begintrace",
                "sequence": identifier
            }
        
        if implicitendtrace is not None:
            message["implicitendtrace"] = implicitendtrace
        
        response = send_to_server(message)
        
        self.assertNotIn("error", response)
        self.assertIn("concolicadvice", response)
        self.assertEqual(response["concolicadvice"], u"done")
    
    def concolicEndTrace(self, identifier):
        message = {
                "command": "concolicadvice",
                "action": "endtrace",
                "sequence": identifier
            }
        
        response = send_to_server(message)
        
        self.assertNotIn("error", response)
        self.assertIn("concolicadvice", response)
        self.assertEqual(response["concolicadvice"], u"done")
    
    def concolicAdvice(self, identifier, amount=None, allowduringtrace=None):
        message = {
                "command": "concolicadvice",
                "action": "advice",
                "sequence": identifier
            }
        
        if amount is not None:
            message["amount"] = amount
        
        if allowduringtrace is not None:
            message["allowduringtrace"] = allowduringtrace
        
        response = send_to_server(message)
        
        self.assertNotIn("error", response)
        self.assertIn("concolicadvice", response)
        self.assertEqual(response["concolicadvice"], u"done")
        self.assertIn("sequence", response)
        self.assertEqual(response["sequence"], unicode(identifier))
        self.assertIn("values", response)
        return response["values"]
    
    def concolicStatistics(self, identifier):
        message = {
                "command": "concolicadvice",
                "action": "statistics",
                "sequence": identifier
            }
        
        response = send_to_server(message)
        
        self.assertNotIn("error", response)
        self.assertIn("concolicadvice", response)
        self.assertEqual(response["concolicadvice"], u"done")
        self.assertIn("statistics", response)
        return response["statistics"]

class AnalysisServerConcolicAdviceApiTests(AnalysisServerConcolicAdviceTestBase):
    
    def test_invalid_command(self):
        self.loadFixture("concolic-simple.html")
        
        message = {
                "command": "concolicadvice"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_invalid_action(self):
        self.loadFixture("concolic-simple.html")
        
        message = {
                "command": "concolicadvice",
                "action": "no-such-action",
                "sequence": "TestSequence"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_missing_action(self):
        self.loadFixture("concolic-simple.html")
        
        message = {
                "command": "concolicadvice",
                "sequence": "TestSequence"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_missing_sequence(self):
        self.loadFixture("concolic-simple.html")
        
        message = {
                "command": "concolicadvice",
                "action": "begintrace"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_empty_sequence(self):
        self.loadFixture("concolic-simple.html")
        
        message = {
                "command": "concolicadvice",
                "action": "begintrace",
                "sequence": ""
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_concolicadvice_without_page_load(self):
        message = {
                "command": "concolicadvice",
                "action": "begintrace",
                "sequence": "TestSequence"
            }
        
        response = send_to_server(message)
        
        self.assertIn("error", response)
    
    def test_advice_before_trace(self):
        self.loadFixture("concolic-simple.html")
        
        advice_message = {
                "command": "concolicadvice",
                "action": "advice",
                "sequence": "TestSequence"
            }
        
        advice_response = send_to_server(advice_message)
        
        self.assertIn("error", advice_response)
    
    def test_endtrace_without_start(self):
        self.loadFixture("concolic-simple.html")
        
        end_message = {
                "command": "concolicadvice",
                "action": "endtrace",
                "sequence": "TestSequence"
            }
        
        end_response = send_to_server(end_message)
        
        self.assertIn("error", end_response)
    
    def test_endtrace_after_different_start_sequence(self):
        self.loadFixture("concolic-simple.html")
        
        begin_message = {
                "command": "concolicadvice",
                "action": "begintrace",
                "sequence": "TestSequence"
            }
        
        begin_response = send_to_server(begin_message)
        
        self.assertNotIn("error", begin_response)
        
        end_message = {
                "command": "concolicadvice",
                "action": "endtrace",
                "sequence": "SomeOtherSequence"
            }
        
        end_response = send_to_server(end_message)
        
        self.assertIn("error", end_response)
    
    def test_begintrace_during_trace(self):
        self.loadFixture("concolic-simple.html")
        
        begin_message = {
                "command": "concolicadvice",
                "action": "begintrace",
                "sequence": "TestSequence"
            }
        
        begin_response = send_to_server(begin_message)
        
        self.assertNotIn("error", begin_response)
        
        begin_message_2 = {
                "command": "concolicadvice",
                "action": "begintrace",
                "sequence": "TestSequence"
            }
        
        begin_response_2 = send_to_server(begin_message_2)
        
        self.assertIn("error", begin_response_2)
    
    def test_advice_during_trace(self):
        self.loadFixture("concolic-simple.html")
        
        begin_message = {
                "command": "concolicadvice",
                "action": "begintrace",
                "sequence": "TestSequence"
            }
        
        begin_response = send_to_server(begin_message)
        
        self.assertNotIn("error", begin_response)
        
        advice_message = {
                "command": "concolicadvice",
                "action": "advice",
                "sequence": "TestSequence"
            }
        
        advice_response = send_to_server(advice_message)
        
        self.assertIn("error", advice_response)
    
    def test_empty_trace_then_advice(self):
        self.loadFixture("concolic-simple.html")
        
        # Record an empty trace
        self.concolicBeginTrace("TestSequence")
        self.concolicEndTrace("TestSequence")
        
        # Get advice and check there are no values.
        values = self.concolicAdvice("TestSequence")
        
        self.assertEqual(values, [])
    
    def test_simple_trace_then_advice(self):
        self.loadFixture("concolic-simple.html")
        
        # Record an action sequence
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # We are still on the form page.
        self.assertUrl(fixture_url_with_scheme("concolic-simple.html"))
        
        # Get advice and check it's what we expect.
        values = self.concolicAdvice("TestSequence")
        
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"testme"
                    }
                ]
            ]
        
        self.assertEqual(values, expected_values)
    
    def test_simple_trace_then_advice_from_result_page(self):
        self.loadFixture("concolic-simple.html")
        
        # Record an action sequence
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "testme")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # We are now on the result page (about:blank)
        self.assertUrl(u"about:blank?")
        
        # Get advice and check it's what we expect.
        values = self.concolicAdvice("TestSequence")
        
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u""
                    }
                ]
            ]
        
        self.assertEqual(values, expected_values)
    
    @unittest.skip("TODO")
    def test_simple_trace_then_advice_from_result_page_with_execution(self):
        self.loadFixture("concolic-simple-to-interesting-result-page.html")
        
        # Record a trace which causes a page load, then end.
        # TODO: Should we see only the original-page-prefix, or the bit including the onload constraints?
    
    @unittest.skip("TODO")
    def test_trace_record_across_page_loads(self):
        self.loadFixture("concolic-simple-to-interesting-result-page.html")
        
        # Record a trace as above which loads a new page, but then do some actions on the new page before ending.
        # TODO: What should we see for this case?
    
    @unittest.expectedFailure # TODO: Decide what the correct behaviour is in this case.
    def test_branches_during_page_load(self):
        self.loadPage("about:blank")
        
        self.concolicBeginTrace("TestSequence")
        self.loadFixture("concolic-onload-constraints.html")
        self.concolicEndTrace("TestSequence")
        
        # We expect to record the form related branches which are in the window.onload handler.
        values = self.concolicAdvice("TestSequence")
        
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"testme"
                    }
                ]
            ]
        
        self.assertEqual(values, expected_values)
    
    def test_advice_returns_only_one_assignment_by_default(self):
        self.loadFixture("concolic-multiple-branches.html")
        
        # Record a trace.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Getting advice should only return one piece by default, even though there are several in total.
        values = self.concolicAdvice("TestSequence")
        
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test1"
                    }
                ]
            ]
        
        self.assertEqual(values, expected_values)
    
    def test_simple_trace_then_multiple_advice(self):
        # Get some advice, then confirm you can get more (by requesting more than the total remaining amount).
        self.loadFixture("concolic-multiple-branches.html")
        
        # Record a trace.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Get the advice in multiple batches.
        values_1 = self.concolicAdvice("TestSequence", 3)
        
        expected_values_1 = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test1"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test2"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test3"
                    }
                ]
            ]
        
        self.assertEqual(values_1, expected_values_1)
        
        values_2 = self.concolicAdvice("TestSequence", 3)
        
        expected_values_2 = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test4"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test5"
                    }
                ]
            ]
        
        self.assertEqual(values_2, expected_values_2)
    
    def test_simple_trace_then_all_advice(self):
        # Get all advice, then confirm there is no more advice remaining.
        self.loadFixture("concolic-multiple-branches.html")
        
        # Record a trace.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Get the advice
        values_1 = self.concolicAdvice("TestSequence", 0)
        
        expected_values_1 = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test1"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test2"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test3"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test4"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"test5"
                    }
                ]
            ]
        
        self.assertEqual(values_1, expected_values_1)
        
        # There is no advice remaining as we got it all in the first batch.
        values_2 = self.concolicAdvice("TestSequence")
        
        self.assertEqual(values_2, [])
    
    def test_trace_then_advice_then_trace_to_complete_exploration(self):
        self.loadFixture("concolic-simple.html")
        
        # As above in test_simple_trace_then_advice, but then record a new trace and confirm that there are no more
        # suggestions.
        
        # Record an action sequence
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Get advice and check it's what we expect.
        values = self.concolicAdvice("TestSequence")
        
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"testme"
                    }
                ]
            ]
        
        self.assertEqual(values, expected_values)
        
        # Perform the same actions again with the new values
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "testme")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Request advice and confirm there is no more.
        values_2 = self.concolicAdvice("TestSequence")
        
        self.assertEqual(values_2, [])
    
    def test_no_more_advice_after_suggestions_exhausted(self):
        self.loadFixture("concolic-simple.html")
        
        # As above in test_trace_then_advice_then_trace_to_complete_exploration, except we do not execute the second 
        # trace... Once it is suggested there is already no more advice to give.
        
        # Record an action sequence
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Get advice and check it's what we expect.
        values = self.concolicAdvice("TestSequence")
        
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"testme"
                    }
                ]
            ]
        
        self.assertEqual(values, expected_values)
        
        # Request advice and confirm there is no more, even without recording the newly suggested trace.
        values_2 = self.concolicAdvice("TestSequence")
        
        self.assertEqual(values_2, [])
    
    def test_record_duplicate_traces(self):
        # Recording a new trace which is the same as an old one makes no difference.
        self.loadFixture("concolic-simple.html")
        
        # Record an action sequence
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Get advice and check it's what we expect.
        values_1 = self.concolicAdvice("TestSequence")
        
        expected_values_1 = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"testme"
                    }
                ]
            ]
        
        self.assertEqual(values_1, expected_values_1)
        
        # Record the exact same trace again.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # There is no new advice... nothing has changed.
        values_2 = self.concolicAdvice("TestSequence")
        
        self.assertEqual(values_2, [])
    
    def test_new_exploration_leads_to_new_suggestion(self):
        # After getting "no more advice" we record the suggested trace and it gives some new advice.
        self.loadFixture("concolic-multi-constraint-int.html")
        
        # Record an execution trace
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Get all advice
        values_1 = self.concolicAdvice("TestSequence", 0)
        
        expected_values_1 = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"123"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"4568"
                    }
                ]
            ]
        
        self.assertEqual(values_1, expected_values_1)
        
        # Confirm there is no more advice.
        values_2 = self.concolicAdvice("TestSequence", 0)
        self.assertEqual(values_2, [])
        
        # Record a new trace, which will expose new branches.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "123")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Confirm there is now more advice available.
        values_3 = self.concolicAdvice("TestSequence", 0)
        
        expected_values_3 = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"890"
                    }
                ]
            ]
        
        self.assertEqual(values_3, expected_values_3)
    
    def test_advice_with_different_types(self):
        # Different field types lead to values of different data-types inthe advice command.
        self.loadFixture("concolic-all-field-types.html")
        
        # Record a trace.
        self.concolicBeginTrace("TestSequence")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Get the advice
        values = self.concolicAdvice("TestSequence", 0)
        
        expected_last_suggestion = [
                {
                    u"field": u"//input[@id='my-radio-button']",
                    u"value": True
                },
                {
                    u"field": u"//input[@id='my-radio-button-2']",
                    u"value": False
                },
                {
                    u"field": u"//input[@id='my-check-box']",
                    u"value": True
                },
                {
                    u"field": u"//select[@id='my-select-box-accessed-by-index']",
                    u"value": 0
                },
                {
                    u"field": u"//select[@id='my-select-box']",
                    u"value": u"Hello"
                },
                {
                    u"field": u"//input[@id='my-text-box']",
                    u"value": u"Hello"
                }
            ]
        
        self.assertEqual(len(values), 5)
        self.assertEqual(values[-1], expected_last_suggestion)
    
    def test_advice_allowduringtrace_flag(self):
        self.loadFixture("concolic-simple.html")
        
        # Record trace 1
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Begin recording trace 2
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "testme")
        self.click("//button")
        
        # Request advice mid-trace.
        # Normally this would not be allowed as per test_advice_during_trace.
        values = self.concolicAdvice("TestSequence", 0, True)
        
        # Advice only knows about trace 1
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"testme"
                    }
                ]
            ]
        
        self.assertEqual(values, expected_values)
        
        # Finishing off the trace as normal gives no error.
        self.concolicEndTrace("TestSequence")
    
    def test_begintrace_implicitendtrace_flag(self):
        self.loadFixture("concolic-simple.html")
        
        # Begin recording trace 1
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        
        # Record trace 2 without explicitly ending trace 1
        # Normally this would not be allowed as per test_begintrace_during_trace
        self.concolicBeginTrace("TestSequence", True)
        self.formInput("id('testinput')", "testme")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Confirm the advice accounts for both traces having been recorded into the tree correctly.
        values = self.concolicAdvice("TestSequence")
        self.assertEqual(values, [])
    
    @unittest.skip("TODO")
    def test_advice_from_multiple_sequences(self):
        pass
    
    @unittest.skip("TODO")
    def test_advice_from_multiple_sequences_interleaved(self):
        pass
    
    @unittest.skip("TODO")
    def test_page_load_during_trace(self):
        pass
    
    @unittest.skip("TODO")
    def test_unrecorded_actions_have_no_effect(self):
        pass
    
    def test_select_restrictions(self):
        self.loadFixture("concolic-select-restrictions.html")
        
        # Record an initial trace
        self.concolicBeginTrace("TestSequence")
        # N.B. Leaving out the forminput command here tests the case of the "base" form field restrictions.
        # If we fill the field it will get overwritten by the dynamic form field support.
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # There should be no suggestions returned, as the only branch is unsatisfiable if we model select restrictions.
        values = self.concolicAdvice("TestSequence")
        
        self.assertEqual(values, [])
    
    def test_radio_restrictions(self):
        self.loadFixture("concolic-radio-restrictions.html")
        
        # Record an initial trace
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput_o1')", True)
        self.formInput("id('testinput_o2')", False)
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # There should be only one suggestion returned, as the branch where both are checked is unsatisfiable if we
        # model radio restrictions.
        # The suggested advice should also force o2 to be true because the constraint is trying to set o1 false.
        values = self.concolicAdvice("TestSequence")
        
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput_o1']",
                        u"value": False
                    },
                    {
                        u"field": u"//input[@id='testinput_o2']",
                        u"value": True
                    }
                ]
            ]
        
        self.assertEqual(values, expected_values)
    
    def test_select_restrictions_dynamic(self):
        self.loadFixture("concolic-select-restrictions-dynamic.html")
        
        # Record an initial trace, with country UK
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('country')", "uk")
        self.formInput("id('city')", "london")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Record a second trace with country Denmark
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('country')", "dk")
        self.formInput("id('city')", "copenhagen")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Now we expect to see suggestions which have correctly matched city/country values.
        # The incorrectly matched branches (e.g. UK and Aarhus) are unsatisfiable and are not returned.
        values = self.concolicAdvice("TestSequence", 0)
        
        expected_values = [
                [
                    {
                        u"field": u"//select[@id='country']",
                        u"value": u"?"
                    }
                ],
                [
                    {
                        u"field": u"//select[@id='country']",
                        u"value": u"uk"
                    },
                    {
                        u"field": u"//select[@id='city']",
                        u"value": u"oxford"
                    }
                ],
                [
                    {
                        u"field": u"//select[@id='country']",
                        u"value": u"dk"
                    },
                    {
                        u"field": u"//select[@id='city']",
                        u"value": u"aarhus"
                    }
                ],
                [
                    {
                        u"field": u"//select[@id='country']",
                        u"value": u"us"
                    }
                ]
            ]
        
        self.maxDiff = None
        self.assertEqual(values, expected_values)
    
    def test_concolic_tree_statistics(self):
        # Record two traces, get some advice, then fetch the statistics.
        self.loadFixture("concolic-multiple-branches.html")
        
        # Record trace 1.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Record trace 2.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "test3")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Get some of the available advice.
        values_1 = self.concolicAdvice("TestSequence", 3)
        
        # Get the statistics
        stats = self.concolicStatistics("TestSequence")
        
        expected = {
                u"Alerts": 1,
                u"ConcreteBranchesFullyExplored": 0,
                u"ConcreteBranchesTotal": 0,
                u"CouldNotSolve": 0,
                u"EndFailure": 0,
                u"EndSuccess": 0,
                u"EndUnknown": 2,
                u"InterestingDomModifications": 0,
                u"Missed": 0,
                u"PageLoads": 1,
                u"Queued": 3,
                u"SymbolicBranchesFullyExplored": 0,
                u"SymbolicBranchesTotal": 0,
                u"TracesRecordedInTree": 2,
                u"Unexplored": 1,
                u"UnexploredSymbolicChild": 4,
                u"Unsat": 0
            }
        self.assertEqual(stats, expected)
    



class AnalysisServerConcolicAdviceLimitations(AnalysisServerConcolicAdviceTestBase):
    @unittest.skip("TODO")
    def test_symbolic_info_is_always_on(self):
        # The server mode suffers from the test-before-inject issue in order to not require resets between each trace.
        pass
    
    @unittest.skip("TODO")
    def test_browser_reset_clears_symbolic_info(self):
        # Same test as above but with a browser reset between trace recordings.
        pass
    
    @unittest.skip("TODO")
    def test_symbolic_info_leakage_between_traces(self):
        # Another limitation of the server mode is that symbolic information can be saved from one trace and used in
        # another. This is also because we do not want to reset the browser between traces.
        pass
    
    @unittest.skip("TODO")
    def test_reset_fixes_symbolic_info_leakage_between_traces(self):
        # Same test as above but with a browser reset between trace recordings.
        pass
    
    def test_delegation_support_not_used_in_server_mode(self):
        self.loadFixture("concolic-symbolic-target.html")
        
        # Record a trace.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # With delegation support enabled, the concolic engine could suggest an assignment but with no form values,
        # so it returns [[]]. We do not enable symbolic event.target in server mode, so no advice is returned.
        values = self.concolicAdvice("TestSequence")
        self.assertEqual(values, [])

    


class AnalysisServerTraceDivergenceTests(AnalysisServerConcolicAdviceTestBase):
    # Partly to check the divergence support is working in server mode.
    # Partly because some aspects of the divergence support can't easily be tested directly from concolic mode.
    
    def test_server_divergence_one_empty_trace(self):
        # Record one normal and one empty trace.
        self.loadFixture("concolic-simple.html")
        
        # Record the first (normal) trace.
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('testinput')", "")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Record an empty trace into the same concolic tree.
        self.concolicBeginTrace("TestSequence")
        self.concolicEndTrace("TestSequence")
        
        # Check advice is what we would expect from the fist trace only.
        values = self.concolicAdvice("TestSequence")
        expected_values = [
                [
                    {
                        u"field": u"//input[@id='testinput']",
                        u"value": u"testme"
                    }
                ]
            ]
        self.assertEqual(values, expected_values)
        
        # Check the graph is what we would expect.
        graph = self.get_graph(self.name())
        self.assertIsNotNone(graph)
        
        expected_graph = """
start -> diverge_0;
diverge_0 -> marker_1;
marker_1 -> marker_2;
marker_2 -> aggr_3;
aggr_3 -> sym_5;
sym_5 -> alt_5;
alt_5 -> end_u_6;
sym_5 -> unexp_queued_7;
diverge_0 -> end_u_8;
"""
        expected_graph = expected_graph.split("\n")[1:-1]
        
        self.assertEqual(graph, expected_graph)
    
    def test_server_divergence_mismatched_trace_recording(self):
        # Record two traces into the same tree which use different elements.
        self.loadFixture("concolic-all-field-types.html")
        
        # Record the first trace
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('my-text-box')", "Wrong Value")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        
        # Record a conflicting trace
        self.formInput("id('my-text-box')", "Hello") # Reset the form
        self.concolicBeginTrace("TestSequence")
        self.formInput("id('my-select-box')", "Welcome")
        self.click("//button")
        self.concolicEndTrace("TestSequence")
        # This trace would add new explorations to the tree [it explores new code in validate()] except that it cannot
        # be merged with the initial trace because of the mismatching marker nodes.
        
        # The advice is as if we had never recorded the second trace at all.
        values = self.concolicAdvice("TestSequence", 0)
        expected_values = [
                [
                    {
                        "field": "//input[@id='my-text-box']",
                        "value": "Hello"
                    }
                ]
            ]
        self.assertEqual(values, expected_values)
        
        # Check the graph is what we would expect.
        graph = self.get_graph(self.name())
        self.assertIsNotNone(graph)
        
        expected_graph = """
start -> diverge_0;
diverge_0 -> marker_1;
marker_1 -> marker_2;
marker_2 -> aggr_3;
aggr_3 -> sym_5;
sym_5 -> alt_5;
alt_5 -> end_u_6;
sym_5 -> unexp_queued_7;
diverge_0 -> marker_8;
marker_8 -> marker_9;
marker_9 -> aggr_10;
aggr_10 -> sym_12;
sym_12 -> unexp_12;
sym_12 -> sym_14;
sym_14 -> alt_14;
alt_14 -> end_u_15;
sym_14 -> unexp_16;
"""
        expected_graph = expected_graph.split("\n")[1:-1]
        
        self.assertEqual(graph, expected_graph)


class AnalysisServerConcolicAdviceExamples(AnalysisServerConcolicAdviceTestBase):
    pass



class AnalysisServerTestsWithCustomTestServer(AnalysisServerConcolicAdviceTestBase):
    class NullOutput(object):
        def write(self, _): pass
        def flush(self): pass
    
    def setUp(self):
        super(AnalysisServerTestsWithCustomTestServer, self).setUp()
        
        self._hide_all_test_output = True
        if self._hide_all_test_output:
            self._save_stdout = sys.stdout
            self._save_stderr = sys.stderr
            sys.stdout = self.NullOutput()
            sys.stderr = self.NullOutput()
        
        self.test_server = BackgroundTestServer()
        self.test_server.start()
        self.test_server_url = "http://%s:%s" % (TEST_SERVER_HOST, TEST_SERVER_PORT)
    
    def tearDown(self):
        try:
            self.test_server.stop()
            time.sleep(0.5)
            
        finally:
            if self._hide_all_test_output:
                sys.stdout = self._save_stdout
                sys.stderr = self._save_stderr
            
            super(AnalysisServerTestsWithCustomTestServer, self).tearDown()
    
    


class AnalysisServerAsyncEventsTests(AnalysisServerTestsWithCustomTestServer):
    
    def test_timers_queueing(self):
        # Identical test to test_ajax_queueing but using timers for the delays.
        
        # The fixture has validation done in a sequence of timers over a 4s period.
        # If we record traces without leaving enough space for this to happen the timers will trigger during subsequent
        # trace recordings and give inconsistent traces.
        
        self.loadFixture("concolic-timers.html")
        
        # Record the first trace
        self.concolicBeginTrace("Seq A")
        self.formInput("id('field1')", "One")
        self.formInput("id('field2')", "Two")
        self.formInput("id('field3')", "Wrong")
        self.click("//button")
        
        # Do not wait long enough; cut the trace off too early.
        time.sleep(2.5)
        self.concolicEndTrace("Seq A")
        
        values_a = self.concolicAdvice("Seq A", 0)
        graph_a = self.get_graph(self.name(), 1)
        
        # Record the second trace
        self.concolicBeginTrace("Seq B")
        self.formInput("id('field1')", "One")
        self.formInput("id('field2')", "Two")
        self.formInput("id('field3')", "Wrong")
        self.click("//button")
        
        # Wait the full time so we capture all execution.
        time.sleep(5)
        self.concolicEndTrace("Seq B")
        
        values_b = self.concolicAdvice("Seq B", 0)
        graph_b = self.get_graph(self.name(), 2)
        
        # Check the returned advice.
        expected_advice_in_synchronous_case = [
                [
                    {
                        u"field": u"//input[@id='field1']",
                        u"value": u"One"
                    },
                    {
                        u"field": u"//input[@id='field2']",
                        u"value": u"Two"
                    },
                    {
                        u"field": u"//input[@id='field3']",
                        u"value": u"Three"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='field1']",
                        u"value": u"One"
                    },
                    {
                        u"field": u"//input[@id='field2']",
                        u"value": u""
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='field1']",
                        u"value": u""
                    }
                ]
            ]
        
        self.assertEqual(values_a, expected_advice_in_synchronous_case)
        self.assertEqual(values_b, expected_advice_in_synchronous_case)
        
        # Check the trees
        expected_tree_in_synchronous_case = """
start -> marker_0;
marker_0 -> marker_1;
marker_1 -> marker_2;
marker_2 -> marker_3;
marker_3 -> aggr_4;
aggr_4 -> sym_6;
sym_6 -> aggr_6;
aggr_6 -> sym_8;
sym_8 -> aggr_8;
aggr_8 -> sym_10;
sym_10 -> unexp_queued_10;
sym_10 -> aggr_11;
aggr_11 -> end_u_12;
sym_8 -> unexp_queued_13;
sym_6 -> unexp_queued_14;
        """
        expected_tree_in_synchronous_case = expected_tree_in_synchronous_case.split("\n")[1:-1]
        
        self.assertEqual(graph_a, expected_tree_in_synchronous_case)
        self.assertEqual(graph_b, expected_tree_in_synchronous_case)
    
    def test_ajax_queueing(self):
        # See also: AnalysisServerFeatureTests.test_event_command_blocking_for_XHR_async
        # Identical test to test_timers_queueing but using AJAX requests for the delays.
        
        # The fixture has validation done in a sequence of timers over a 4s period.
        # If we record traces without leaving enough space for this to happen the timers will trigger during subsequent
        # trace recordings and give inconsistent traces.
        
        self.loadFixture("concolic-ajax.html")
        
        # Record the first trace
        self.concolicBeginTrace("Seq A")
        self.formInput("id('field1')", "One")
        self.formInput("id('field2')", "Two")
        self.formInput("id('field3')", "Wrong")
        self.click("//button")
        
        # Do not wait long enough; cut the trace off too early.
        time.sleep(2.5)
        self.concolicEndTrace("Seq A")
        
        values_a = self.concolicAdvice("Seq A", 0)
        graph_a = self.get_graph(self.name(), 1)
        
        # Record the second trace
        self.concolicBeginTrace("Seq B")
        self.formInput("id('field1')", "One")
        self.formInput("id('field2')", "Two")
        self.formInput("id('field3')", "Wrong")
        self.click("//button")
        
        # Wait the full time so we capture all execution.
        time.sleep(5)
        self.concolicEndTrace("Seq B")
        
        values_b = self.concolicAdvice("Seq B", 0)
        graph_b = self.get_graph(self.name(), 2)
        
        # Check the returned advice.
        expected_advice_in_synchronous_case = [
                [
                    {
                        u"field": u"//input[@id='field1']",
                        u"value": u"One"
                    },
                    {
                        u"field": u"//input[@id='field2']",
                        u"value": u"Two"
                    },
                    {
                        u"field": u"//input[@id='field3']",
                        u"value": u"Three"
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='field1']",
                        u"value": u"One"
                    },
                    {
                        u"field": u"//input[@id='field2']",
                        u"value": u""
                    }
                ],
                [
                    {
                        u"field": u"//input[@id='field1']",
                        u"value": u""
                    }
                ]
            ]
        
        self.assertEqual(values_a, expected_advice_in_synchronous_case)
        self.assertEqual(values_b, expected_advice_in_synchronous_case)
        
        # Check the trees
        expected_tree_in_synchronous_case = """
start -> marker_0;
marker_0 -> marker_1;
marker_1 -> marker_2;
marker_2 -> marker_3;
marker_3 -> aggr_4;
aggr_4 -> sym_6;
sym_6 -> aggr_6;
aggr_6 -> sym_8;
sym_8 -> aggr_8;
aggr_8 -> sym_10;
sym_10 -> unexp_queued_10;
sym_10 -> aggr_11;
aggr_11 -> end_u_12;
sym_8 -> unexp_queued_13;
sym_6 -> unexp_queued_14;
        """
        expected_tree_in_synchronous_case = expected_tree_in_synchronous_case.split("\n")[1:-1]
        
        self.assertEqual(graph_a, expected_tree_in_synchronous_case)
        self.assertEqual(graph_b, expected_tree_in_synchronous_case)
    
    def test_async_event_sequencing(self):
        # Test page has a variety of nested timers and AJAX requests on each event.
        # The server mode is expected to force these to be executed in a deterministic fixed order.
        
        self.loadFixture("async-event-queueing.html")
        
        # We expect all the pageload events to be complete before the server returns from the pageload.
        # N.B. Only 4 "rounds" of interval timers are executed.
        # N.B. The two interval timers are interleaved because of this "rounds" system.
        s1 = "Load; XHR-0; XHR-100; XHR-500; XHR-1000; Load-finished; Timeout-0; Timeout-100; Timeout-500; Timeout-2000; Interval-500 [1/5]; Interval-2-500 [1/2]; Interval-500 [2/5]; Interval-2-500 [2/2]; Interval-500 [3/5]; Interval-500 [4/5]; "
        self.assertStatusElementContains(s1)
        
        # Trigger events and check they also include the associated async events in the call.
        self.click("id('click-a')")
        s2 = s1 + "Click-A; XHR-A-500; Timeout-A-100; XHR-A-100 [From T-100]; Timeout-A-200; XHR-A-200 [From T-200]; Timeout-A-100 [From X-500]; "
        self.assertStatusElementContains(s2)
        
        self.click("id('click-b')")
        s3 = s2 + "Click-B; XHR-B-Recursive-100 [1/5]; XHR-B-Recursive-100 [2/5]; XHR-B-Recursive-100 [3/5]; XHR-B-Recursive-100 [4/5]; XHR-B-Recursive-100 [5/5]; Timeout-B-100; Timeout-B-200; "
        self.assertStatusElementContains(s3)
        
        # N.B. The ajax requests and timers are called in registration order, not timer order.
        self.click("id('click-c')")
        s4 = s3 + "Click-C; XHR-C-200; XHR-C-100; Timeout-C-200; Timeout-C-100; "
        self.assertStatusElementContains(s4)
        
        # N.B. Only 4 "rounds" of nested timers are fired.
        self.click("id('click-d')")
        s5 = s4 + "Click-D; Timeout-D-Nested-100 [1/5]; Timeout-D-Nested-100 [2/5]; Timeout-D-Nested-100 [3/5]; Timeout-D-Nested-100 [4/5]; "
        self.assertStatusElementContains(s5)
        
        # There should be no more events remaining and nothing will trigger "in the background".
        time.sleep(3)
        self.assertStatusElementContains(s5)
        
        # N.B. The results from this test are expected to differe slightly from a normal browser.
        # First, the events are put in a deterministic order, which has all AJAX events fired synchronously before the
        # timers, and the timers fired in a browser-specified order which is not necessarily chronological.
        # Second, timers over 4 levels of "nesting" are cleared without being executed to avoid an infinite loop.
    
    
    






class ArtemisCrash(Exception):
    pass

class ErrorCatchingTestResult(unittest.TextTestResult):
    def addError(self, test, err):
        # If the error is a URLError then we replace it with ArtemisCrash
        if isinstance(err[1], urllib2.URLError) and err[1].reason.errno == 111 :
            err = (ArtemisCrash, ArtemisCrash(err[1]), err[2])
        
        # Otherwise report this error as normal.
        super(ErrorCatchingTestResult, self).addError(test, err)
    


def fixture_url(page):
    """Returns the (local) URL for a given test page."""
    return os.path.join(FIXTURE_ROOT, page)

def fixture_url_with_scheme(page):
    """Returns the file://... URL for a given test page."""
    return u"file://" + fixture_url(page)

def run_artemis_server(test_name="test"):
    """
    Runs Artemis in server mode and returns the PID which can be used to check on it or kill it.
    
    We can't use the harness.execute_artemis() method, as it waits until the run is finished and returns its results.
    """
    
    output_dir = os.path.join(OUTPUT_DIR, test_name)
    if os.path.isdir(output_dir):
        shutil.rmtree(output_dir)
    os.makedirs(output_dir)
    
    cmd = [ARTEMIS_EXEC] + ["--major-mode", "server", "--analysis-server-port", str(ARTEMIS_SERVER_PORT), "-v", "all", "--analysis-server-log"]
    
    if DEBUG_SHOW_ARTEMIS_OUTPUT:
        p = subprocess.Popen(cmd, cwd=output_dir)
    else:
        p = subprocess.Popen(cmd, cwd=output_dir, stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    
    # Wait for the server to come up (max 1s).
    i = 0
    connected = False
    s = socket.socket()
    while i < 10 and not connected:
        try:
            s.connect(("localhost", 8008))
        except socket.error:
            pass # Server is not up yet.
        else:
            s.close()
            connected = True
        time.sleep(0.1)
        i += 1
    
    return p


def send_to_server(message, encode_json=True, timeout=None, return_urllib_response=False):
    """Sends a command to the running server and returns the result."""
    
    time.sleep(0.1) # A small wait here to allow the server to settle down makes the test suite more reliable.
    
    if encode_json:
        data = json.dumps(message)
    else:
        data = str(message)
    
    response = urllib2.urlopen(ARTEMIS_SERVER_URL, data, timeout)
    
    if return_urllib_response:
        return response
    else:
        return json.load(response)


def check_no_existing_server():
    no_server = False
    try:
        # Just check we can open the URL without an exception
        urllib2.urlopen(ARTEMIS_SERVER_URL)
    except:
        no_server = True
    
    return no_server

if __name__ == '__main__':
    if check_no_existing_server():
        # Hack to support the "-v" option again. Something about the custom testRunner is breaking it.
        verbosity = 2 if "-v" in sys.argv else 1
        unittest.main(buffer=True, catchbreak=True, testRunner=unittest.TextTestRunner(resultclass=ErrorCatchingTestResult, verbosity=verbosity))
    else:
        print "There is already a server running at %s which will affect the tests." % ARTEMIS_SERVER_URL
