
WebKit Hacking
==============

Exporting Symbols in WebKit
---------------------------

By default, all symbols (functions, classes, ect.) are hidden in the compiled WebKit library. Only a subset of symbols (primarily Qt related) are exposed and usable from Artemis.

A list of all exported symbols is stored in ``WebKit/Source/qtwebkit-export.map``. Edit this file to export new symbols.

