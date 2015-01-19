
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

Commands
^^^^^^^^

* ``echo``
    Returns the text provided in the ``message`` field.
    
    Send: ``{"command": "echo", "message": "Hello, World"}``
    
    Recieve: ``{"message": "Hello, World"}``
    
* ``exit``
    Shuts down the server.
    
    Send: ``{"command":"exit"}``
    
    Recieve: ``{"message", "Server is shutting down"}``
    
* ``pageload``
    Not yet implemented.




