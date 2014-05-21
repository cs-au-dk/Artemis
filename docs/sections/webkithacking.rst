
WebKit Hacking
==============

Exporting Symbols in WebKit
---------------------------

By default, all symbols (functions, classes, ect.) are hidden in the compiled WebKit library. Only a subset of symbols (primarily Qt related) are exposed and usable from Artemis.

A list of all exported symbols is stored in ``WebKit/Source/qtwebkit-export.map``. Edit this file to export new symbols.

Instrumenting the DOM
---------------------

The DOM API in WebKit is auto generated from a set of IDL files specifying the exact API and its behavior. Artemis introduces instrumentation into this layer partly by modifying the IDL files and partly by modifying the perl script processing the idl files.

The perl script can be found in ``WebKit/Source/WebCore/bindings/scripts/CodeGeneratorJS.pm``.

IDL files can be found in these folders:

 * ``WebKit/Source/WebCore/html``
 * ``WebKit/Source/WebCore/dom``
