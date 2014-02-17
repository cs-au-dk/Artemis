"""
Creates a screenshot of a web page with certain XPath entry-points identified.
"""

import sys
import time
import argparse

try:
    from PyQt4.QtCore import QUrl
    from PyQt4.QtGui import QApplication, QImage, QPainter
    from PyQt4.QtWebKit import QWebView
except ImportError:
    print "The 'PyQt4' module is required by this script."
    print "Alternatively, PyQt4.QtWebKit may be trying to use our modified WebKit and failing."
    print "You may need to modify LD_LIBRARY_PATH for this script. Try the entrypoint-identifier.sh wrapper script."
    sys.exit()


def main():
    # Handle the arguments.
    parser = DefaultHelpParser(description="Creates a screenshot of a web page with certain XPath entry-points identified.")
    parser.add_argument('url', help="The URL to display.")
    parser.add_argument('outfile', help="The image file to output.")
    parser.add_argument('xpath', nargs='*', help="The XPath expression(s) to identify on the page.")
    args = parser.parse_args()
    
    print "Loading", args.url
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
        self.load(QUrl(url))
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
        # Adjust the viewport to see the whole page.
        frame = self.page().mainFrame()
        self.page().setViewportSize(frame.contentsSize())
        # Save the image
        image = QImage(self.page().viewportSize(), QImage.Format_ARGB32)
        painter = QPainter(image)
        frame.render(painter)
        painter.end()
        print 'Saving', outfile
        image.save(outfile)
    
    def addxpath(self, xpath, label):
        """Adds a label to the display which identifies the single node matched by the given XPath expression."""
        print "Adding identifier", label
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
        self.page().currentFrame().evaluateJavaScript(js_injection)
    


# An argument parser which prints the help message after an error.
# Adapted from http://stackoverflow.com/a/3637103/1044484
class DefaultHelpParser(argparse.ArgumentParser):
    def error(self, message):
        sys.stderr.write('Error: %s\n' % message)
        self.print_help()
        sys.exit(2)


if __name__ == "__main__":
    main()
