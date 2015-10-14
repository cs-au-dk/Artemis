#!/usr/bin/env python

"""
A server which returns different JavaScript code on different requests for the same page.
This is for testing the divergent merge support in Artemis.
"""

import BaseHTTPServer
import threading
import re

import urllib2
import time


HOST_NAME = 'localhost'
PORT = 8099

class JsInjectionRequestHandler(BaseHTTPServer.BaseHTTPRequestHandler):
    
    def do_HEAD(self):
        """Respond to a HEAD request."""
        
        self.send_response(200)
        self.send_header("Content-type", "text/html")
        self.end_headers()
    
    def do_GET(self):
        """Respond to a GET request."""
        
        # Work out what iteration we are on.
        match = re.search("ArtemisIteration=(\d+)", self.path)
        artemis_iteration = 0
        if match is not None:
            artemis_iteration = int(match.group(1))
        
        self.send_response(200)
        self.send_header("Content-type", "text/html")
        self.end_headers()
        
        self.wfile.write("<html>\n")
        self.wfile.write("<head>\n")
        self.wfile.write("  <title>Inconsistent Server</title>\n")
        self.wfile.write("  <script type=\"text/javascript\">\n")
        self.wfile.write("    function validate() {\n")
        self.wfile.write("      " + self._current_js(artemis_iteration).replace("\n", "\n      ") + "\n")
        self.wfile.write("    }\n")
        self.wfile.write("  </script>\n")
        self.wfile.write("</head>\n")
        self.wfile.write("<body>\n")
        self.wfile.write("  <form method=\"GET\" action=\"about:blank\" >\n")
        self.wfile.write("    " + self._current_html(artemis_iteration).replace("\n", "\n    ") + "\n")
        self.wfile.write("  </form>\n")
        self.wfile.write("</body>\n")
        self.wfile.write("</html>\n")
    
    def _current_js(self, artemis_iteration):
        if hasattr(self.server, "js_injection"):
            if artemis_iteration not in range(len(self.server.js_injection)):
                return "alert('No JS injection found for iteration " + str(artemis_iteration) + "');"
            else:
                return self.server.js_injection[artemis_iteration]
        else:
            return "alert('No JS injection found.');"
    
    def _current_html(self, artemis_iteration):
        if hasattr(self.server, "html_injection") and self.server.html_injection is not None:
            if artemis_iteration not in range(len(self.server.html_injection)):
                return "<p>No HTML injection found for iteration " + str(artemis_iteration) + "</p>"
            else:
                return self.server.html_injection[artemis_iteration]
        else:
            return "<input type=\"text\" id=\"testinput\" />\n<button type=\"submit\" onclick=\"return validate()\" >Submit</button>"
    

class JsInjectionServer(BaseHTTPServer.HTTPServer):
    def set_js_injection(self, js_injection):
        self.js_injection = js_injection
    
    def set_html_injection(self, html_injection):
        self.html_injection = html_injection
    


def start_server_with_js_injections(js_list, html_list=None):
    def execute_server(stop_event):
        # Handles one request with each of the JS injections, then shuts down.
        server = JsInjectionServer((HOST_NAME, PORT), JsInjectionRequestHandler)
        
        server.set_js_injection(js_list)
        server.set_html_injection(html_list)
        while not stop_event.is_set():
            server.handle_request()
        server.server_close()
    
    # Run the server in a new thread so we can return immediately.
    stop_evt = threading.Event()
    server_thread = threading.Thread(target=execute_server, args=(stop_evt,))
    server_thread.daemon = True # Kill the thread when the rest of the program ends, instead of hanging.
    server_thread.start()
    return server_thread, stop_evt






def main_testing_server_via_thread():
    js1 = "var x = document.getElementById('testinput'); if (x.value == 'testme') { return true; } else { alert('Error'); return false; }"
    server_thread, stop_event = start_server_with_js_injections([js1]*100)
    
    print "Server started..."
    
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        pass
    
    print "\nStopping..."
    
    stop_event.set()
    try:
        urllib2.urlopen('http://localhost:%s/clear-final-request-handler' % PORT)
    except:
        print "Could not connect to server to clear final request handler."
    time.sleep(0.1)
    print "Alive?", server_thread.is_alive()


def main_testing_server_as_if_in_test_suite():
    server_thread, stop_event = start_server_with_js_injections(["alert(\"Run A\");", "alert(\"Run B\");", "alert(\"Run C\");"])
    
    print "Server started..."
    
    # Seems not to be required.
    time.sleep(0.1)
    
    print "Sending queries..."
    
    for i in range(3):
        print filter(lambda x: "alert" in x, urllib2.urlopen('http://localhost:%s/test?ArtemisIteration=%s' % (PORT, i)).readlines())
        #time.sleep(1)
    
    stop_event.set()
    try:
        urllib2.urlopen('http://localhost:%s/clear-final-request-handler' % PORT)
    except:
        print "Could not connect to server to clear final request handler."
    
    print "Server should be stopped now..."
    print "Alive? ", server_thread.is_alive()
    


if __name__ == "__main__":
    main_testing_server_via_thread()
    #main_testing_server_as_if_in_test_suite()







