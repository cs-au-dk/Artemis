# ArtForm

ArtForm is the name for the form- and interface-analysis modes of Artemis.

[Main Artemis Readme](README.md)

ArtForm uses concolic execution to explore different execution paths of JavaScript code attached to web forms.

For more information, see: [www.cs.ox.ac.uk/projects/ArtForm/](http://www.cs.ox.ac.uk/projects/ArtForm/)

A demo screencast is available at: [www.cs.ox.ac.uk/projects/ArtForm/demo/](http://www.cs.ox.ac.uk/projects/ArtForm/demo/)


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

For full details on the advice API, see [the server mode documentation](docs/sections/server.rst), and [concolic execution in advice mode](docs/sections/server-concolic-advice.rst).

An example call might be:

    artemis --major-mode server --analysis-server-port 8008  --analysis-server-log --coverage-report html --analysis-server-debug-view

At which point the API commands can be sent:

    $ curl -w "\n" --data '{"command":"pageload","url":"http://www.example.com"}' localhost:8008
    { "pageload" : "done", "url" : "http://www.example.com/" }
    $ curl -w "\n" --data '{"command":"element","element":"//h1"}' localhost:8008
    { "elements" : [ "<h1>Example Domain</h1>" ] }



# ArtForm source code

ArtForm is implemented as a set of new modes for the original Artemist tool.
There are significant updates and chnges throughout Artemis, but the key new components are as follows:

* The main controlling code (called a `Runtime`) for each of the new modes: [concolic](artemis-code/src/runtime/toplevel/concolicruntime.h), [concolic standalone](artemis-code/src/runtime/toplevel/concolicstandaloneruntime.h) (without forms support), [manual](artemis-code/src/runtime/demomode/demowindow.h), and [advice server](artemis-code/src/runtime/toplevel/analysisserverruntime.h).
* [The symbolic interpreter](WebKit/Source/JavaScriptCore/symbolic), and [symbolic expressions](WebKit/Source/JavaScriptCore/symbolic/expression)
* The creation of fresh symbolic values: [directly](WebKit/Source/JavaScriptCore/symbolic/expression) (see `globalFuncArtemisInput*`), and [from forms](WebKit/Source/WebCore/bindings/scripts/CodeGeneratorJS.pm) (this is the code generator for the relevant JS DOM API, search for `ARTEMIS` or `SymbolicInputElement`; the code is generated from [modified IDL files here](WebKit/Source/WebCore/html))
* [Input simulation](artemis-code/src/runtime/input/clicksimulator.cpp)
* [Form modelling](artemis-code/src/runtime/input/forms)
* [The JSON server which forms the API for advice mode](artemis-code/src/runtime/analysisserver)
* [The path trace reporting](artemis-code/src/model/pathtracer.h)
* [The coverage report](artemis-code/src/model/coverage) (from the original Artemis)
* [The main concolic advice infrastructure](artemis-code/src/concolic), including:
    * [The concolic execution angine](artemis-code/src/concolic/concolicanalysis.h)
    * [The different search procedures](artemis-code/src/concolic/search)
    * [Constraint solving](artemis-code/src/concolic/solver)
    * [Tracking form field dependencies](artemis-code/src/concolic/handlerdependencytracker.h)
    * [Representation of symbolic traces and the execution tree](artemis-code/src/concolic/executiontree)
    * [Trace classification](artemis-code/src/concolic/executiontree/classifier)
* [Automated test suites](artemis-code/tests/system) for concolic and server modes, and various parts of the symbolic infrastructure
* [A proxy which rewrites JavaScript code into an un-minified form](proxies/prettifyproxy.js)

Further documentation of the low-level changes within WebKit is in the [docs](docs) directory ([or online](https://artemis.readthedocs.io/en/latest/)).
In particular, see [Concolic Testing Framework](docs/sections/concolic.rst), [Concolic infrastructure test mode](docs/sections/concolic-standalone.rst), [Server Mode](docs/sections/server.rst), and [Server Mode - Concolic Advice](docs/sections/server-concolic-advice.rst).



