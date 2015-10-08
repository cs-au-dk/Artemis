#!/usr/bin/env python

"""
A server which returns different JavaScript code on different requests for the same page.
This is for testing the divergent merge support in Artemis.
"""

import BaseHTTPServer
import threading

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
        
        self.send_response(200)
        self.send_header("Content-type", "text/html")
        self.end_headers()
        
        self.wfile.write("<html>\n")
        self.wfile.write("<head>\n")
        self.wfile.write("  <title>Inconsistent Server</title>\n")
        self.wfile.write("  <script type=\"text/javascript\">\n")
        self.wfile.write("    function validate() {\n")
        self.wfile.write("      " + self._current_JS().replace("\n", "\n      ") + "\n")
        self.wfile.write("    }\n")
        self.wfile.write("  </script>\n")
        self.wfile.write("</head>\n")
        self.wfile.write("<body>\n")
        self.wfile.write("  <form method=\"GET\" action=\"about:blank\" >\n")
        self.wfile.write("    <input type=\"text\" id=\"testinput\" />\n")
        self.wfile.write("    <button type=\"submit\" onclick=\"return validate()\" >Submit</button>\n")
        self.wfile.write("  </form>\n")
        self.wfile.write("</body>\n")
        self.wfile.write("</html>\n")
        
    
    def _current_JS(self):
        if hasattr(self.server, "jsInjection"):
            return self.server.jsInjection
        else:
            return "alert(\"No JS injection found.\");"
    

class JsInjectionServer(BaseHTTPServer.HTTPServer):
    def setJsInjection(self, jsString):
        self.jsInjection = jsString


def start_server_with_js_injections(jsList):
    def execute_server():
        # Handles one request with each of the JS injections, then shuts down.
        server = JsInjectionServer((HOST_NAME, PORT), JsInjectionRequestHandler)
        for jsString in jsList:
            server.setJsInjection(jsString)
            server.handle_request()
        server.server_close()
    
    # Run the server in a new thread so we can return immediately.
    server_thread = threading.Thread(target=execute_server)
    server_thread.daemon = True # Kill the thread when the rest of the program ends, instead of hanging.
    server_thread.start()
    return server_thread






def main_testing_server_directly():
    server = JsInjectionServer((HOST_NAME, PORT), JsInjectionRequestHandler)
    try:
        #server.setJsInjection("alert(\"HELLO\");")
        #server.serve_forever()
        while 1:
            server.setJsInjection("alert(\"Run A\");")
            server.handle_request()
            server.setJsInjection("alert(\"Run B\");")
            server.handle_request()
            server.setJsInjection("alert(\"Run C\");")
            server.handle_request()
    except KeyboardInterrupt:
        pass
    server.server_close()

def main_testing_server_via_thread():
    start_server_with_js_injections(["alert(\"Run A\");", "alert(\"Run B\");", "alert(\"Run C\");"])
    
    print "Server started..."

def main_testing_server_as_if_in_test_suite():
    srv = start_server_with_js_injections(["alert(\"Run A\");", "alert(\"Run B\");", "alert(\"Run C\");"])
    
    print "Server started..."
    
    # Seems not to be required.
    time.sleep(0.1)
    
    print "Sending queries..."
    
    for _ in range(3):
        print filter(lambda x: "alert" in x, urllib2.urlopen('http://localhost:%s' % PORT).readlines())
        #time.sleep(1)
    
    print "Server should be stopped now..."
    print "Alive? ", srv.is_alive()
    


if __name__ == "__main__":
    #main_testing_server_directly()
    
    #main_testing_server_via_thread()
    
    main_testing_server_as_if_in_test_suite()







