# ArtForm

ArtForm is the name for the form- and interface-analysis modes of Artemis.

[Main Artemis Readme](README.md)

ArtForm uses concolic execution to explore different execution paths of JavaScript code attached to web forms.

For more information, see: [www.cs.ox.ac.uk/projects/ArtForm/](http://www.cs.ox.ac.uk/projects/ArtForm/)


## Installation
The [main installation instructions](INSTALL) already include everything required for ArtForm.

## Manual mode

Manual mode is used to manually interact with a web page and see what information is recorded by our symbolic tracing infrastructure.

As an example, try:

    artemis --major-mode manual --path-trace-report html --coverage-report html http://www.example.com

Some small synthetic examples are offered when just running:

    artemis --major-mode manual

## Concolic mode

The concolic mode uses concolic execution to automatically explore the JavaScript code attached to web forms.

An example call mgiht be:

    artemis --major-mode concolic --concolic-tree-output final-overview -i 0 --concolic-event-sequences simple --concolic-event-handler-report --concolic-search-procedure selector --concolic-selection-procedure "round-robin(avoid-unsat:random)" --concolic-selection-budget 50 --coverage-report html --concolic-button "//xpath/to/the/submit/button" http://www.example.com

Here we have provided the URL of the page to analyse, and an XPath expression to identify the form's submit button.
ArtForm will load the page, and fill each form field before clicking the submit button.
This forms a single iteration or symbolic trace.
Whenever a form input value is used to control the JavaScript execution (e.g. in form validation code), ArtForm's concolic execution will generate new input values to excercise that code path and test them on a subsequent iteration.

## Advice server mode

ArtForm can also run in an "advice server" mode, where the browser can be controlled externally via a JSON API.
The client sends browser commands and can control the concolic execution - recording symbolic traces and requesting new suggested values.

For full details on the advice API, see [the server mode documentation](https://artemis.readthedocs.io/en/latest/sections/server.html), and [concolic execution in advice mode](https://artemis.readthedocs.io/en/latest/sections/server-concolic-advice.html).

An example call might be:

    artemis --major-mode server --analysis-server-port 8008  --analysis-server-log --coverage-report html --analysis-server-debug-view

At which point the API commands can be sent:

    $ curl -w "\n" --data '{"command":"pageload","url":"http://www.example.com"}' localhost:8008
    { "pageload" : "done", "url" : "http://www.example.com/" }
    $ curl -w "\n" --data '{"command":"element","element":"//h1"}' localhost:8008
    { "elements" : [ "<h1>Example Domain</h1>" ] }
