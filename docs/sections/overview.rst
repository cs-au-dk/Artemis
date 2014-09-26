
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

The Artemis tool is written in C++ using Qt 4.8 and the *qmake* build system. The main qmake project file is ``artemis-code/artemis-code.pro``, which in turn includes ``artemis-code/artemis-core.pri`` (the latter is also included by the unit-test project).

The central classes are shown in the following diagram:

.. graphviz::

	digraph overview {

		"Runtime" -> "WebKitExecutor";
		"Runtime" -> "InputGeneratorStrategy";
		"Runtime" -> "WorkList";
		"InputGeneratorStrategy" -> "ExecutionResult";
		"WebKitExecutor" -> "ExecutionResult";
		"WebKitExecutor" -> "AppModel";
		"WorkList" -> "PrioritizerStrategy";
		"PrioritizerStrategy" -> "AppModel";
	}

The main application loop and initialization of the application resides in ``Runtime`` (``runtime/runtime.h``). The main application loop maintains the ``WorkList`` (``runtime/worklist/worklist.h``), using an instance of ``InputGeneratorStrategy`` (``strategies/inputgenerator/inputgeneratorstrategy.h``) to generate new event sequences for the worklist. Event sequences are executed using an instance of ``WebKitExecutor`` (``runtime/browser/webkitexecutor.h``), responsible for all interaction with the instrumented WebKit library described in the next section. Finally, the ``WebKitExecutor`` gathers the feedback from WebKit in an ``ExecutionResult`` (``runtime/browser/executionresult.h``) and in updates to ``AppModel`` (``model/appmodel.h``), used by other parts of Artemis. 

WebKit Instrumentation
----------------------

We instrument WebKit (checkout anno 2011-12-28) to observe the execution of the tested application, gathering feedback for subsequent iterations. 

The WebKit code-base is extended with a JavaScript debugger (``WebKit/Source/WebCore/instrumentation/listenerdebugger.h``) and a number of listening-points boxed in ``ifdef ARTEMIS`` and ``endif`` directives. The debugger and listening-points invoke methods on a global instance of ``QWebExecutionListener`` (``/WebKit/Source/WebKit/qt/Api/qwebexecutionlistener.h``), denoted the *execution listener*. 

The execution listener provides a `Qt signal interface <http://qt-project.org/doc/qt-4.8/signalsandslots.html>`_ used by Artemis for gathering feedback. In general, each method invocation from a listening-point is translated and emitted as a signal. Furthermore, the execution listener translates from the WebKit world into the Qt world, such as translating WebKit's StringImpl class into Qt's QString. As a rule, WebKit related types is not allowed in Artemis, and Qt related types is only allowed in the execution listener (and other Qt provided classes making up the WebKit-Qt interface).
