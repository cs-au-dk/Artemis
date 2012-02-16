This is the README for v8-convert (a.k.a. cvv8).

Project home:

    http://code.google.com/p/v8-juice/wiki/V8Convert

That page has (or links to) lots of documentation and
example code.

------------------------------------------------------
Installing:

The library is header-only. Simply copy include/cvv8 to somewhere in your
includes path.

------------------------------------------------------
Building the demo code:

The basic demo code can be built with:

   cd examples
   make

It requires GNU Make and gcc (or hack it to suit your system).

Project files for MS Visual Studio 2010 can be found under
./build/vs_10.

There are several full-featured demonstrations in the 'addons' directory.


------------------------------------------------------
Re-configuring it for different argument list length limits...

If you find that you _really_ need to bind functions with huge number of
arguments (more than 10) you may need to increase the sizes of the generated
typelist code. See the Makefile for how this is done.
