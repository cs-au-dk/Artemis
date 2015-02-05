
Server Mode
===========

With ``--major-mode server`` Artemis runs an 'analysis server' with a JSON interface for controlling it externally and
reporting what it finds.

In this mode **all** other arguments except those prefixed by ``analysis-server-*`` are ignored, including the URL.


The API
-------

The server runs on port 8008 by default. This can be changed with the ``--analysis-server-port`` option.

Calls to the server are expected to POST a JSON message with the following format::

    {
        "command": "pageload",
        "url": "http://www.example.com"
    }

We do not use REST-style URLs to avoid the complications of URL-encoding complex strings like URLs or XPaths.

The ``command`` property must always be set, and the rest of the properties depend on which command was used.

There is an echo command which can be used to check the server is running::

    curl -w "\n" --data '{"command":"echo","message":"Hello, World"}' localhost:8008

This should return::

    {
        "message": "Hello, World"
    {

Only one command can be sent per request. The server is designed to be blocking; any requests sent while another is
still being processed will return an error.

Commands
^^^^^^^^

* ``echo``
    Used for testing. Returns the text provided in the ``message`` field. The optional ``delay`` field is the number
    of seconds to delay before sending back the response (integers 0--30 are valid).
    
    Send::
    
        {
            "command": "echo",
            "message": "Hello, World",
            "delay": 1
        }
    
    Recieve: ``{"message": "Hello, World"}``
    
* ``exit``
    Shuts down the server.
    
    Send: ``{"command": "exit"}``
    
    Recieve: ``{"message", "Server is shutting down"}``
    
* ``pageload``
    Loads a URL in the Artemis browser. The final URL we end up on after redirects etc. is returned.
    
    The optional ``timeout`` parameter is the number of milliseconds to wait before cancelling the load and returning
    an error (integers 0--30000 accepted), 0 implies no timeout.
    
    Send::
    
        {
            "command": "pageload",
            "url": "http://www.example.com",
            "timeout": 5000
        }
    
    Recieve::
    
        {
            "pageload": "done",
            "url": "http://www.example.com"
        }
    
* ``handlers``
    Lists the event handlers registered on the current page. The list returned is a list of XPath expressions
    identifying the DOM element each handler is registered on.
    
    There must already have been a page load command issued.
    
    Send: ``{"command": "handlers"}``
    
    Recieve: (e.g for the handlers.html test case) ::
    
        {
            "handlers": [
                {
                    "event": "click",
                    "element": "//a[@id=\"dom-attr\"]"
                },
                {
                    "event": "click",
                    "element": "//a[@id=\"js-attr\"]"
                },
                {
                    "event": "click",
                    "element": "//a[@id=\"listener\"]"
                }
            ]
        }
    
* ``click``
    Clicks on an element specified by XPath.
    
    For now then only type of click is a JavaScript-level click, with no option for a GUI click.
    
    Send::
    
        {
            "command": "click",
            "element": "id(\"clickable\")"
        }
    
    Recieve: ``{"click": "done"}``
    
* ``dom``
    Returns a string representation of the current DOM.
    
    Send: ``{"command": "dom"}``
    
    Recieve: ``{"dom": "<html> ... </html>"}``
    
* ``fieldsread``
    Returns a list of the form fields which have been read by different events since the last page load.
    
    Send: ``{"command": "fieldsread"}``
    
    Recieve: (e.g. from form.html test page) ::
    
        {
            "fieldsread": [
                {
                    "element": "//button[1]",
                    "event": "click",
                    "reads": [
                        {
                            "count": 2,
                            "field": "//input[@id='first']"
                        }
                    ]
                },
                {
                    "element": "//button[2]",
                    "event": "click",
                    "reads": [
                        {
                            "count": 1,
                            "field": "//input[@id='second']"
                        }
                    ]
                },
                {
                    "element": "//button[3]",
                    "event": "click",
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
    
    Each "event object" contains the event type triggered and target element (XPath as passed in via the ``click``
    command), and a list of the form fields which were read by the handler for that event. Each of these "read objects"
    contains an XPath to the field and a count of the number of times the field value was read (at a low level in the
    JavaScript interpreter).
    

