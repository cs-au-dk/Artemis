.. _server:

Server Mode
===========

With ``--major-mode server`` Artemis runs an 'analysis server' with a JSON interface for controlling it externally and
reporting what it finds.

In this mode **all** other arguments except those prefixed by ``analysis-server-*`` are ignored, including the URL.

There is a debug view which shows the internal browser, which is shown when the option ``--analysis-server-debug-view``
is given.

The concolic advice mode is documented at :ref:`server-concolic-advice`.

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
--------

* ``echo``
    Used for testing. Returns the text provided in the ``message`` field. The optional ``delay`` field is the number
    of seconds to delay before sending back the response (integers 0--30 are valid).
    
    Send::
    
        {
            "command": "echo",
            "message": "Hello, World",
            "delay": 1
        }
    
    Receive: ``{"message": "Hello, World"}``
    
* ``exit``
    Shuts down the server.
    
    Send: ``{"command": "exit"}``
    
    Receive: ``{"message", "Server is shutting down"}``
    
* ``pageload``
    Loads a URL in the Artemis browser. The final URL we end up on after redirects etc. is returned.
    
    The optional ``timeout`` parameter is the number of milliseconds to wait before cancelling the load and returning
    an error (integers 0--3600000 accepted), 0 implies no timeout.
    
    Send::
    
        {
            "command": "pageload",
            "url": "http://www.example.com",
            "timeout": 5000
        }
    
    Receive::
    
        {
            "pageload": "done",
            "url": "http://www.example.com"
        }
    
* ``backbutton``
    Uses the browser history to go back one page.
    
    It is an error to call this command before there are at least two pages in the history.
    Due to an implementation issue, "about:blank" is never accessible via this command.
    
    Send: ``{"command": "backbutton"}``
    
    Receive::
    
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
    
    Receive: (e.g for the handlers.html test case) ::
    
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
    
    It is also possible to specify a filter (by XPath) and receive only the handlers registered on matching elements.
    
    Send::
    
        {
            "command": "handlers",
            "filter": "id('listener')"
        }
    
    Receive: (e.g for the handlers.html test case) ::
    
        {
            "handlers": [
                {
                    "element": "//a[@id='listener']",
                    "events": ["click", "focus"]
                }
            ]
        }
    
    The XPath identifiers returned are Artemis' internally generated ones and may not match the filter, even if it
    selects a single element.
    
* ``click``
    Clicks on an element specified by XPath.
    
    For now then only type of click is a JavaScript-level click, with no option for a GUI click.
    
    N.B. This is now just a special case of the newer ``event`` command.
    
    Send::
    
        {
            "command": "click",
            "element": "id(\"clickable\")"
        }
    
    Receive: ``{"click": "done"}``
    
    There is an optional ``method`` field, which allows you to choose the type of click performed.
    Possible values are:
    
    ``simple`` (default)
        Just generates a click event, in the saem way as the ``event`` command would.
    
    ``simulate-js``
        Uses JavaScript events to simulate a user click.
    
    ``simulate-gui``
        Uses GUI events to simulate a click.
        
        N.B. This click is done by clicking the coordinates at the centre of the element. If the element is behind
        another element or the element bounding box is larger than the clickable/visible area, this command can miss
        and click the wrong thing.
    
    Send::
    
        {
            "command": "click",
            "element": "id(\"clickable\")",
            "method": "simulate-js"
        }
    
    Receive: ``{"click": "done"}``
    
    
* ``event``
    Triggers a JavaScript event on the element at the specified XPath. (Or custom event; see below.)
    
    N.B. Event names are given as "change" or "focus, not "onchange", "onfocus", etc.
    
    Send (e.g. on handlers.html)::
    
        {
            "command": "event",
            "element": "id(\"listener\")",
            "event": "focus"
        }
    
    Receive: ``{"event": "done"}``
    
    There are also some custom Artemis event types which are not the standard JavaScript events.
    These are handled separately by Artemis and are not triggered as JavaScript events directly.
    
    So far there is only one implemented: for pressing ``Enter`` on a form field (e.g. to submit the form).
    
    Send (e.g. on form-submission.html)::
    
        {
            "command": "event",
            "element": "id(\"input-text\")",
            "event": "ARTEMIS-press-enter"
        }
    
    Receive: ``{"event": "done"}``
    
* ``page``
    Returns information about the current page (the URL, page title, and DOM statistics).
    
    Send: ``{"command": "page"}``
    
    Receive::
    
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
            "dom": true
        }
    
    Receive::
    
        {
            "url": "http://www.example.com",
            "title": "Example Domain",
            "dom": "<html> ... </html>",
            "elements": 12,
            "characters": 1262
        }
    
* ``element``
    Returns the string representation of each element (if any) matching a given XPath.
    
    Send: (e.g. for the click.html test page) ::
    
        {
            "command": "element",
            "element": "id(\"clickable\")"
        }
    
    Receive::
    
        {
            "elements": [ "<a href=\"\" id=\"clickable\">Click here to add new buttons to the page.</a>" ]
        }
    
    There is also an optional ``property`` field which will return the string representation of that object property
    instead.
    
    Send::
    
        {
            "command": "element",
            "element": "id(\"clickable\")",
            "property": "nodeName"
        }
    
    Receive::
    
        {
            "elements": [ "A" ]
        }
    
* ``fieldsread``
    Returns a list of the form fields which have been read by different events since the last page load.
    
    Send: ``{"command": "fieldsread"}``
    
    Receive: (e.g. from form.html test page) ::
    
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
    The method of injection can be changed with the optional ``method`` parameter (see below).
    
    Send::
    
        {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world."
        }
    
    Receive: ``{"forminput": "done"}``
    
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
    
    There is a ``method`` field, which allows you to choose the type of injection performed.
    Possible values are:
    
    ``inject``
        Inject the value into the ``.value`` property (depending on the input type; see above).
    
    ``onchange`` (default)
        Inject the value and trigger the ``onchange`` handler for the form field.
    
    ``simulate-js``
        Uses JavaScript events to simulate a user filling the form field as closely as possible.
        The support for text inputs is currently much more sophisticated than for checkboxes, radio buttons, and
        select boxes.
        
        When ``simulate-js`` is used, an extra optional property ``noblur`` can be set to boolean ``true`` to stop the
        'blur' (de-focus) event being triggered on this element once the injection is complete. This can be useful (for
        example) to stop auto-complete boxes being hidden when the field is deselected.
    
    ``simulate-gui``
        Not yet implemented.
    
    Send::
    
        {
            "command": "forminput",
            "field": "id('input-text')",
            "value": "Hello, world.",
            "method": "inject"
        }
    
    Receive: ``{"forminput": "done"}``
    
* ``xpath``
    Evaluates an XPath query and returns the result.
    
    The result may be a String, Number, Boolean or Node-Set. Node-sets are represented as an array of the string
    representations of the nodes.
    
    Node-set (all examples on the click.html test case)::
    
        {
            "command": "xpath",
            "xpath": "//h1"
        }
    
    ::
    
        {
            "result": [ "<h1>Clickable elements</h1>" ] 
        }
    
    String::
    
        {
            "command": "xpath",
            "xpath": "string(//h1)"
        }
    
    ::
    
        {
            "result": "Clickable elements"
        }
    
    Number::
    
        {
            "command": "xpath",
            "xpath": "string-length(string(//h1))"
        }
    
    ::
    
        {
            "result": 18
        }
    
    Boolean::
    
        {
            "command": "xpath",
            "xpath": "string-length(string(//h1)) > 10"
        }
    
    ::
    
        {
            "result": true
        }
    
    It is also possible to provide a list of XPaths to evaluate. The result will be a list of the results of each XPath
    as above::
    
        {
            "command": "xpath",
            "xpath": [
                "//h1",
                "string(//h1)",
                "string-length(string(//h1))",
                "string-length(string(//h1)) > 10"
            ]
        }
    
    ::
    
        {
            "result": [
                [ "<h1>Clickable elements</h1>" ],
                "Clickable elements",
                18,
                true
            ]
        }
    
    N.B. Non-matching queries are handled as normal in a browser's XPath evaluation::
    
        //does-not-exist => []
        string(//does-not-exist) => ""
        boolean(//does-not-exist) => false
    
    An XPath which cannot be evaluated (because it is invalid) will return an error.
    
* ``windowsize``
    Set the size of the browser window.
    
    Send::
    
        {
            "command": "windowsize",
            "width": 1024,
            "height": 768
        }
    
    Receive: ``{ "windowsize": "done" }``
    
* ``concolicadvice``
    Allows the server to record traces nito a concolic execution tree and return advice about new form field values
    which can lead to new exploration.
    
    See the :ref:`server-concolic-advice` documentation for details.
    
* ``evaluate-js``
    Evaluates a JavaScript string on the current page.
    
    Send::
    
        {
            "command": "evaluatejs",
            "js": "document.getElementById('clickable').click()"
        }
    
    Receive: ``{ "evaluatejs": "done" }``
    
* ``setsymbolicvalues``
    Sets the internal symbolic values of variables accessed via ``artemisInputBoolean()``, ``artemisInputInteger()``,
    and ``artemisInputString()``. This can be used for testing the internal concolic engine of the platform.
    For normal testing of web pages the ``forminput`` command should be used instead for concolic testing.
    
    The ``values`` parameter is a mapping from variable names (strings) to values, whihc may be strings, integers or
    booleans.
    
    The ``reset`` parameter is optional, and if set to ``true``, the internal symbolic value table will be cleared
    before setting these replacement values.
    
    Send::
    
        {
            "command": "setsymbolicvalues",
            "values": {
                    "X": "Hello",
                    "Y": 123,
                    "Z": true
                },
            "reset": true
        }
    
    Receive: ``{ "setsymbolicvalues": "done" }``
    
    Now a call like the following would update the DOM with the injected symbolic values::
    
        {
            "command": "evaluatejs",
            "js": "document.getElementById('status').textContent = artemisInputString('X') + ' ' + artemisInputInteger('Y') + ' ' + artemisInputBoolean('Z');"
        }
    
* ``coverage``
    Returns a report of the line coverage from the executed commands.
    The line coverage is taken since the server was strted, and cannot be reset.
    
    The ``report`` is a list of reports for each distinct JavaScript source (web page, JS file, etc.).
    The line-by-line coverage report is human-readable, not in a good machine-readable format.
    It can be parsed with analyse-coverage.py.
    
    The ``linescovered`` parameter is a list of line numbers whihc were covered.
    
    N.B. A line is considered covered if some interpretation was done on that line. So the close-braces of if
    statements, else statements, blank lines, and so on will never be considered covered.
    
    Send::
    
        {
            "command": "coverage"
        }
    
    Receive::
    
        {
            "coverage": [
                    {
                        "url": "...",
                        "line": "...",
                        "linescovered": [...]
                        "report": "..."
                    },
                    {
                        ...
                    }
                ]
        }
    











