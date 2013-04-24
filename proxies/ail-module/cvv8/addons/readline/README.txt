This is a minimalist v8-juice plugin for a GNU Readline-like
interface.  In actuallity it supports GNU Readline, BSD Editline, and
stdin as input sources, but for purposes of this plugin it's
configured to use GNU Readline.

This is part of the v8-juice project:

http://code.google.com/p/v8-juice/

========================================================================
BUILDING AND INSTALLING

You must have libv8-juice-config in your path (it is installed by the
libv8-juice installation). Then...

      ~> make
      ~> make install

That will copy the plugin to the default v8-juice plugins directory,
ready for use from libv8-juice client code.

========================================================================
USING THE PLUGIN

To use it from JS code, call readline.read(), passing it a prompt
string:

    var s = readline.read("prompt: ");
    if( undefined === s ) {
       // User tapped Ctrl-D or otherwise triggered end of input
    }
    else {
        print("User entered:",s);
    }

If the user taps the EOF sequence (normally Ctrl-D) then undefined is
returned, otherwise the entered string (possibly empty) is returned.

History support:

Readline can remember what you've typed before. To load a history
file, creating it if needed, use:

	bool readline.loadHistory(filename)

To save history file (or it is automatically saved when the Readline
object is destroyed):

	bool Readline.saveHistory(filename)

To clear the input history:

	Readline.clearHistory()

There is not (and won't be) any support for more complex features of
GNU Readline, like custom tab expansions. The reason is simple: the
underlying read handler isn't bound specifically to GNU Readline - it
can use lesser APIs if GNU Readline isn't available (see Readline.hpp
and Readline.cpp for the details).
