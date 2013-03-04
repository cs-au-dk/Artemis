import subprocess
import os
import signal
import time
import re

class WebServer(object):

    def __init__(self, web_root,port): 
        #cmd = 'python -m SimpleHTTPServer %s ' % port
        cmd = 'php -S localhost:%s >/dev/null 2>/dev/null' % port
        self._webserver = subprocess.Popen(cmd, 
            cwd=web_root, 
            shell=True, 
            preexec_fn=os.setsid)

        time.sleep(1) # allow the web-server to start (hack)

    def __del__(self):
        os.killpg(self._webserver.pid, signal.SIGKILL)
