
Concolic infrastructure test mode
=================================

This is a new major-mode for Artemis which runs the concolic analysis on standalone JavaScript snippets.
(The normal concolic mode is specifically designed for form validation analysis and relies on this setting.)


Overview
--------

A single JavaScript file is loaded by Artemis and executed.
The context is a blank web page (because of the architecture of Artemis).

There are three new built-in functions which are used to get inputs for the concolic testing:

+------------------------------+--------------------------------------------------------------+
| Function                     | Concolic input                                               |
+==============================+==============================================================+
| ``artemisInputString("x")``  | Returns a string corresponding to concolic variable ``x``.   |
+------------------------------+--------------------------------------------------------------+
| ``artemisInputInteger("y")`` | Returns an integer corresponding to concolic variable ``y``. |
+------------------------------+--------------------------------------------------------------+
| ``artemisInputBoolean("z")`` | Returns a boolean corresponding to concolic variable ``z``.  |
+------------------------------+--------------------------------------------------------------+

These are called by the input JavaScript code to get the inputs for the code being tested.
Any branches depending on these input values should be explored by the concolic analysis, by substituting new values
during a subsequent iteration.



Example
-------



