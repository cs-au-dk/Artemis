
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
    
* ``backbutton``
    Uses the browser history to go back one page.
    
    It is an error to call this command before there are at least two pages in the history.
    Due to an implementation issue, "about:blank" is never accessible via this command.
    
    Send: ``{"command": "backbutton"}``
    
    Recieve::
    
        {
            "backbutton": "done",
            "url": "http://www.example.com"
        }
    
* ``handlers``
    Lists the event handlers registered on the current page.
    The list returned shows XPath expressions identifying the DOM elements with events, and a list of events attached
    to each.
    The special cases "document" or "window" may also be given as an identifier for events registered on those objects.
    
    There must already have been a page load command issued.
    
    Send: ``{"command": "handlers"}``
    
    Recieve: (e.g for the handlers.html test case) ::
    
        {
            "handlers": [
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
    
* ``page``
    Returns information about the current page (the URL, page title, and DOM statistics).
    
    Send: ``{"command": "page"}``
    
    Recieve::
    
        {
            "url": "http://www.example.com",
            "title": "Example Domain",
            "elements": 12,
            "characters": 1262
        }
    
    The optional "dom" parameter can be set to `True` to include the entire DOM dump.
    
    Send::
    
        {
            "command": "page",
            "dom": True
        }
    
    Recieve::
    
        {
            "url": "http://www.example.com",
            "title": "Example Domain",
            "dom": "<html> ... </html>",
            "elements": 12,
            "characters": 1262
        }
    
* ``element``
    Returns the string representation of each element (if any) matching a gven XPath.
    
    Send: (e.g. for click.html test page) ::
    
        {
            "command": "element",
            "element": "id(\"clickable\")"
        }
    
    Recieve::
    
        {
            "elements": ["<a href=\"\" id=\"clickable\">Click here to add new buttons to the page.</a>"]
        }
    
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
    
* ``forminput``
    Injects values into form fields and triggers their change handlers.
    
    Send::
    
        {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world."
        }
    
    Recieve: ``{"forminput": "done"}``
    
    The valid element types for ``field`` are ``input`` and ``select``.
    
    The ``value`` property can be set to a string (as above), integer, or bool. Strings are used when injecting into
    text fields or select boxes. Integers can be used to inject into a select box by index (sets the ``selectedIndex``
    property to the given value). Booleans are used to inject into inputs with type ``checkbox`` or ``radio``.
    
    The allowable combinations of ``field`` and ``value`` are:
    
    +------------+-------------------------+---------------------+-------------------------+
    |            | ``input``               | ``input`` with type | ``select``              |
    |            | (not checkbox or radio) | checkbox or radio   |                         |
    +============+=========================+=====================+=========================+
    | **String** | Sets ``.value``         | *Invalid*           | Sets ``.value``         |
    +------------+-------------------------+---------------------+-------------------------+
    | **Int**    | *Invalid*               | *Invalid*           | Sets ``.selectedIndex`` |
    +------------+-------------------------+---------------------+-------------------------+
    | **Bool**   | *Invalid*               | Sets ``.checked``   | *Invalid*               |
    +------------+-------------------------+---------------------+-------------------------+
    
    For example, the following commands are all valid on the form-injections.html test case::
    
        {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world."
        }
    
    This one sets the checkbox to ticked::
    
        {
            "command": "forminput",
            "field": "id('input-checkbox')",
            "value": true
        }
    
    When injecting into a select box, the ``value`` attribute of the appropriate ``option`` element must be given,
    which is not necessarily the text which appears in the UI.::
    
        <select id="input-select" >
            <option value="first" >First Option</option>
            <option value="second" >Second Option</option>
            <option value="third" >Third Option</option>
        </select>
    
    This one selects "Third Option" in the UI::
    
        {
            "command": "forminput",
            "field": "id('input-select')",
            "value": "third"
        }
    
    This one also selects "Third Option", by using the index::
    
        {
            "command": "forminput",
            "field": "id('input-select')",
            "value": 2
        }
    
    The form-injections.html example includes a 'marker' element so you can confirm the form input worked::
    
        {
            "command": "element",
            "element": "id('status')"
        }
    
    ::
    
        {
            "elements": [ "<strong id=\"status\">#input-text set to 'Hello, World'</strong>" ]
        }
    













