#!/usr/bin/env python3
"""
Creates a screenshot of a web page with certain XPath entry-points identified.
"""

import sys
import time
import argparse
import os

# Use python3/Qt5 to avoid conflicts with Artemis' own modified version of WebKit.
try:
    from PyQt5.QtCore import QUrl
    from PyQt5.QtWidgets import QApplication
    from PyQt5.QtGui import QImage, QPainter
    from PyQt5.QtWebKitWidgets import QWebView
except ImportError:
    print("The 'PyQt5' module and WebKit bindings are required by this script.")
    print("For example on Ubuntu >= 13.10 you should be able to install python3-pyqt5 and python3-pyqt5.qtwebkit.")
    sys.exit()


def main():
    # Handle the arguments.
    parser = DefaultHelpParser(description="Creates a screenshot of a web page with certain XPath entry-points identified.")
    parser.add_argument('url', help="The URL to display.")
    parser.add_argument('outfile', help="The image file to output.")
    parser.add_argument('xpath', nargs='*', help="The XPath expression(s) to identify on the page.")
    args = parser.parse_args()
    
    print("Loading", args.url)
    display = XPathDisplay(args.url)
    for idx,xpath in enumerate(args.xpath):
        label = "EP %d" % (idx+1)
        display.addxpath(xpath, label)
    display.save(args.outfile)




# Heavily adapted from http://stackoverflow.com/a/12031316/1044484
class XPathDisplay(QWebView):
    """
    Loads a web page and allows identifiers to be added to it by XPath expressions.
    The result can be saved as an image.
    """
    
    def __init__(self, url):
        self.app = QApplication(sys.argv)
        QWebView.__init__(self)
        self._loaded = False # Used within _wait_load.
        self.loadFinished.connect(self._loadFinished)
        # The version of webkit I have prints some stuff to stdout which I do not want.
        # See https://bugreports.qt-project.org/browse/QTBUG-31074
        with suppress_stdout_stderr():
            self.load(QUrl(url))
            #self.show()
            self._wait_load()
    
    def _wait_load(self, delay=0):
        """Waits until the page has loaded."""
        # process app events until page loaded
        while not self._loaded:
            self.app.processEvents()
            time.sleep(delay)
        self._loaded = False
    
    def _loadFinished(self, result):
        self._loaded = True
    
    def save(self, outfile):
        """Saves the current diaplay as an image file."""
        print('Saving', outfile)
        # Adjust the viewport to see the whole page.
        frame = self.page().mainFrame()
        self.page().setViewportSize(frame.contentsSize())
        # Save the image
        image = QImage(self.page().viewportSize(), QImage.Format_ARGB32)
        painter = QPainter(image)
        frame.render(painter)
        painter.end()
        image.save(outfile)
    
    def addxpath(self, xpath, label):
        """Adds a label to the display which identifies the single node matched by the given XPath expression."""
        print("Adding identifier", label)
        xpath = xpath.replace("'", "\\'")
        label = label.replace("'", "\\'")
        js_injection = """
            var matches = document.evaluate('%s', document, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE, null);
            for(var i = 0; i < matches.snapshotLength; i++){
                var element = matches.snapshotItem(i);
                // Outline the element
                element.style.outline = '5px solid lawngreen';
                // Add a label to the element
                var rect = element.getBoundingClientRect();
                var label = document.createElement('span');
                label.appendChild(document.createTextNode('%s'));
                label.style.color = 'magenta';
                label.style.fontSize = '30px';
                label.style.fontFamily = 'sans-serif';
                var pos_x = rect.left;
                var pos_y = rect.top - 40;
                label.style.position = 'absolute';
                label.style.top = pos_y.toString() + 'px';
                label.style.left = pos_x.toString() + 'px';
                document.body.appendChild(label);
            }
        """
        js_injection = js_injection % (xpath, label)
        #print js_injection
        self.page().mainFrame().evaluateJavaScript(js_injection)
    


# An argument parser which prints the help message after an error.
# Adapted from http://stackoverflow.com/a/3637103/1044484
class DefaultHelpParser(argparse.ArgumentParser):
    def error(self, message):
        sys.stderr.write('Error: %s\n' % message)
        self.print_help()
        sys.exit(2)


# Suppress output from WebKit.
# http://stackoverflow.com/q/11130156/1044484
class suppress_stdout_stderr(object):
    '''
    A context manager for doing a "deep suppression" of stdout and stderr in 
    Python, i.e. will suppress all print, even if the print originates in a 
    compiled C/Fortran sub-function.
       This will not suppress raised exceptions, since exceptions are printed
    to stderr just before a script exits, and after the context manager has
    exited (at least, I think that is why it lets exceptions through).      
    '''
    
    def __init__(self):
        # Open a pair of null files
        self.null_fds =  [os.open(os.devnull,os.O_RDWR) for x in range(2)]
        # Save the actual stdout (1) and stderr (2) file descriptors.
        self.save_fds = (os.dup(1), os.dup(2))
    
    def __enter__(self):
        # Assign the null pointers to stdout and stderr.
        os.dup2(self.null_fds[0],1)
        os.dup2(self.null_fds[1],2)
    
    def __exit__(self, *_):
        # Re-assign the real stdout/stderr back to (1) and (2)
        os.dup2(self.save_fds[0],1)
        os.dup2(self.save_fds[1],2)
        # Close the null files
        os.close(self.null_fds[0])
        os.close(self.null_fds[1])



if __name__ == "__main__":
    main()
