
Server Mode
===========

With ``--major-mode server`` Artemis runs an 'analysis server' with a JSON interface for controlling it externally and
reporting what it finds.

In this mode **all** other arguments except those prefixed by ``analysis-server-*`` are ignored, including the URL.


The API
-------

The server runs on port 8099 by default. This can be changed with the ``--analysis-server-port`` option.

Calls to the server are expected to POST a JSON message with the following format::

    {
        "command": "pageload",
        "url": "http://www.example.com"
    }

We do not use REST-style URLs to avoid the complications of URL-encoding complex strings like URLs or XPaths.

The ``command`` property must always be set, and the rest of the properties depend on which command was used.

There is an echo command which can be used to check the server is running::

    curl --data '{"command":"echo","message":"Hello, World"}' localhost:8008

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
            "delay": 1                              [Optional]
        }
    
    Recieve: ``{"message": "Hello, World"}``
    
* ``exit``
    Shuts down the server.
    
    Send: ``{"command": "exit"}``
    
    Recieve: ``{"message", "Server is shutting down"}``
    
* ``pageload``
    Loads a URL in the Artemis browser.
    
    Send::
    
        {
            "command": "pageload",
            "url": "http://www.example.com"
        }
    
    Recieve: ``{"pageload": "done"}``
    
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
    
    For now then only type of lcick is a JavaScript-level click, with no option for a GUI click.
    
    Send::
    
        {
            "command": "click",
            "element": "id(\"clickable\")"
        }
    
    Recieve: ``{"click": "done"}``


