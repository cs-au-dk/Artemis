
The 10 Minute Primer
====================

The repository is divided into four folders:

``artemis-code/``
	Source code, tests and scripts making up the core Artemis tool.

``WebKit/``
	An instrumented version of WebKit.

``ailproxy/``
	A web-proxy for mocking server-side interfaces.

``docs/``
	Source files for the documentation you are reading.

Installation and Usage
----------------------

For installation instructions see the INSTALL file and for usage run the command ``artemis --help``.

The Artemis Tool
----------------

The Artemis tool is written in C++ using Qt 4.8.



WebKit Instrumentation
----------------------

We instrument WebKit to observe the execution of the tested application, gathering feedback for subsequent iterations. 

The WebKit code-base is extended with a JavaScript debugger (``WebKit/Source/WebCore/instrumentation/listenerdebugger.h``) and a number of listening-points boxed in ``ifdef ARTEMIS`` and ``endif`` directives. The debugger and listening-points invoke methods on a global instance of ``QWebExecutionListener`` (``/WebKit/Source/WebKit/qt/Api/qwebexecutionlistener.h``), denoted the *execution listener*. 

The execution listener provides a `Qt signal interface <http://qt-project.org/doc/qt-4.8/signalsandslots.html>`_ used by Artemis for gathering feedback. In general, each method invocation from a listening-point is translated and emitted as a signal. Furthermore, the execution listener translates from the WebKit world into the Qt world, such as translating WebKit's StringImpl class into Qt's QString. As a rule, WebKit related types is not allowed in Artemis, and Qt related types is only allowed in the execution listener (and other Qt provided classes making up the WebKit-Qt interface).