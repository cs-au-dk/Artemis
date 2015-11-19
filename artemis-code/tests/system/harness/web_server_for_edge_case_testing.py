#!/usr/bin/env python

"""
A server which is used to test various edge cases in the concolic analysis and server mode.
"""


import BaseHTTPServer
import SocketServer
import threading
import time
import urllib2
import re


HOST_NAME = 'localhost'
PORT = 8098


class TestServerRequestHandler(BaseHTTPServer.BaseHTTPRequestHandler):
    def do_GET(self):
        """Respond to a GET request."""
        
        self.actions = {
                "":                 self.page_index,
                "404":              self.page_404,
                "echo-path":        self.page_echo_path,
                "slow-response":    self.page_slow_response
            }
        
        # Check the first part of the path to work out which behaviour is required.
        path_parts = self.path.split("/")
        path_prefix = path_parts[1] if len(path_parts) > 1 else ""
        
        if path_prefix in self.actions.keys():
            self.actions[path_prefix]()
        else:
            self.page_404()
    
    def page_404(self):
        self.send_response(404)
        self.send_header("Content-type", "text/html")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        
        self.wfile.write("<html>\n")
        self.wfile.write("<head>\n")
        self.wfile.write("  <title>Test Server</title>\n")
        self.wfile.write("</head>\n")
        self.wfile.write("<body>\n")
        self.wfile.write("  <h1>404</h1>\n")
        self.wfile.write("</body>\n")
        self.wfile.write("</html>\n")
    
    class TestServerHtmlResponseTemplate:
        def __init__(self, request, title):
            self.request = request
            self.title = title
        
        def __enter__(self):
            self.request.send_response(200)
            self.request.send_header("Content-type", "text/html")
            self.request.send_header("Access-Control-Allow-Origin", "*")
            self.request.end_headers()
            
            self.request.wfile.write("<html>\n")
            self.request.wfile.write("<head>\n")
            self.request.wfile.write("  <title>Test Server</title>\n")
            self.request.wfile.write("</head>\n")
            self.request.wfile.write("<body>\n")
            self.request.wfile.write("  <h1>" + str(self.title) + "</h1>\n")
        
        def __exit__(self, type, value, traceback):
            self.request.wfile.write("</body>\n")
            self.request.wfile.write("</html>\n")
    
    def page_index(self):
        with self.TestServerHtmlResponseTemplate(self, "Test Server Index"):
            self.wfile.write("  <ul>\n")
            for (prefix, fn) in self.actions.iteritems():
                self.wfile.write("    <li><a href=\"/" + prefix + "\">/" + prefix + "</a> - " + fn.__name__ + "</li>\n")
            self.wfile.write("  </ul>\n")
            self.wfile.write("  <p>The first part of the path determines the page. For example <code>/echo-path</code> and <code>/echo-path/my/custom/path</code> both lead to <code>page_echo_path</code>.</p>\n")
    
    def page_echo_path(self):
        with self.TestServerHtmlResponseTemplate(self, "Test Server Index"):
            self.wfile.write("  <p>\n")
            self.wfile.write("    Accessed: " + self.path + "\n")
            self.wfile.write("  </p>\n")
    
    def page_slow_response(self):
        # Check if a time was specified.
        # Format /slow-response/X where X is an integer number of milliseconds.
        match = re.match('^/slow-response/(\d+)$', self.path)
        delay = int(match.group(1))/1000.0 if match else 1.0
        
        time.sleep(delay)
        
        with self.TestServerHtmlResponseTemplate(self, "Test Server Slow Response"):
            self.wfile.write("  <p>\n")
            self.wfile.write("    This page was delayed by " + str(delay) + " seconds.\n")
            self.wfile.write("  </p>\n")

class ThreadedHTTPServer(SocketServer.ThreadingMixIn, BaseHTTPServer.HTTPServer):
    """Threaded version of BaseHTTPServer."""
    pass

class BackgroundTestServer:
    """Harness to run the server in a background thread."""
    
    def start(self):
        def server_thread(stop_event, finished_event):
            server = ThreadedHTTPServer((HOST_NAME, PORT), TestServerRequestHandler)
            server.daemon_threads = True
            while not stop_event.is_set():
                server.handle_request()
            server.server_close()
            finished_event.set()
        
        # Run the server in a new thread so we can return immediately.
        print "BackgroundTestServer: Starting..."
        self.stop_evt = threading.Event()
        self.finished_evt = threading.Event()
        self.server_thread = threading.Thread(target=server_thread, args=(self.stop_evt, self.finished_evt))
        self.server_thread.daemon = True # Kill the thread when the rest of the program ends, instead of hanging.
        self.server_thread.start()
    
    def stop(self):
        self.stop_evt.set()
        try:
            urllib2.urlopen('http://localhost:%s/clear-final-request-handler' % PORT)
        except:
            pass #print "BackgroundTestServer: Could not connect to server to clear final request handler."
        
        self.finished_evt.wait(1)
        print "BackgroundTestServer: Stopped..."
        print "BackgroundTestServer: Alive? ", self.server_thread.is_alive()



if __name__ == "__main__":
    print "Test Server"
    print "Running standalone: stop with Ctrl-C."
    
    test_server = BackgroundTestServer()
    test_server.start()
    
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        pass
    
    test_server.stop()
    print "Done"
    
