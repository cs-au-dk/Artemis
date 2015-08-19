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

FIXTURE_ROOT = os.path.join(os.environ['ARTEMISDIR'], 'artemis-code', 'tests', 'system', 'fixtures', 'server')

ARTEMIS_EXEC = 'artemis'
OUTPUT_DIR = '.output'

ARTEMIS_SERVER_PORT = 8008
ARTEMIS_SERVER_URL = 'http://localhost:%s' % ARTEMIS_SERVER_PORT

DEBUG_SHOW_ARTEMIS_OUTPUT = False


class AnalysisServerTestBase(unittest.TestCase):
    
    def setUp(self):
        # Run the server and save a reference so we can kill it in the end.
        self.server = run_artemis_server(self.id())
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
    

class AnalysisServerFeatureTests(AnalysisServerTestBase):
    
    def test_server_process_is_running(self):
        self.assertTrue(self.server.poll() is None)
    
    def test_connect_to_server(self):
        self.assertServerAcceptingConnections()
    
    def test_port_check(self):
        # Run  an extra server and confirm it terminates with an error.
        
        second_server = run_artemis_server(self.id() + "_extra")
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
        page_message = {
            "command": "page"
        }
        
        page_response = send_to_server(page_message)
        
        self.assertIn("url", page_response)
        self.assertEqual(page_response["url"], "about:blank")
    
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
        
        time.sleep(0.5)
        
        self.assertStatusElementContains("Timers: timer-0-fired")
        
        time.sleep(1)
        
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
        # The server is often crashed after the previous call.
        check_response = send_to_server(check_message)
        
        self.assertNotIn("error", check_response)
        
        self.assertIn("url", check_response)
        self.assertEqual(check_response["url"], u"http://www.w3schools.com/php/welcome.php")
        
        self.assertIn("dom", check_response)
        self.assertEqual(check_response["dom"], u"""<!DOCTYPE html><html><head></head><body>

Welcome Test<br>
Your email address is: test@example.com

</body></html>""")
        
    


class AnalysisServerSystemTests(AnalysisServerTestBase):
    pass
    



class ArtemisCrash(Exception):
    pass

class ErrorCatchingTestResult(unittest.TextTestResult):
    def addError(self, test, err):
        # If the error is a ZeroDivisionException then we replace it with CustomException
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
    
    cmd = [ARTEMIS_EXEC] + ["--major-mode", "server", "--analysis-server-port", str(ARTEMIS_SERVER_PORT), "-v", "all"]
    
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
        unittest.main(buffer=True, catchbreak=True, testRunner=unittest.TextTestRunner(resultclass=ErrorCatchingTestResult))
    else:
        print "There is already a server running at %s which will affect the tests." % ARTEMIS_SERVER_URL
