
WebKit Instrumentation
======================

This section documents various modifications made to WebKit as part of our instrumentation.

Note, we require WebKit and specifically the JavaScript Core interpreter to be compiled in a non-JIT mode and in 64bit-mode. That is, we do not support JIT compiling and the 32bit compatible version of WebKit.

Symbolically Enhanced JavaScript Values
---------------------------------------

JavaScript values  in WebKit are NaN encoded 

NaN encoding is used in WebKit to represent JavaScript values, denoted ``JSValue``. Each ``JSValue`` is a 64bit value, either representing a *double*, *integer*, or a *pointer* to a ``JSCell``. A detailed description of this encoding can be found in ``JSValue.h``, ``here <http://wingolog.org/archives/2011/05/18/value-representation-in-javascript-implementations>``_ and ``here <http://en.wikipedia.org/wiki/X86-64#Virtual_address_space_details>``_.

We want to enhance each concrete JavaScript value with a pointer to a symbolic representation of the same value. Furthermore, we want this to be fairly efficient, and only decrease efficiency if a symbolic value is present.

For pointers to ``JSCell`` we extend ``JSCell`` with a pointer to our representation of symbolic values.

If the concrete values are not associated with a symbolic value we use the current NaN encoding for performance. However, for values with associated symbolic values we can't fit in both a pointer to a symbolic value and the concrete value within the constraints of the NaN encoding. In this case, we enhance the current NaN encoding with an additional bit pattern to represent symbolically enhanced integers and doubles.

Specifically, we change the following patterns,

 	Pointer  {  0000:PPPP:PPPP:PPPP
         	  / 0001:****:****:****
	Double   {         ...
         	  \ FFFE:****:****:****
	Integer  {  FFFF:0000:IIII:IIII

into,

 	Pointer  {  0000:PPPP:PPPP:PPPP
         	  / 0001:****:****:****
	Double   {         ...
         	  \ FFFE:****:****:****
    Sym. Int {  FFFF:EPPP:PPPP:PPPP
    Sym. Dbl {  FFFF:FPPP:PPPP:PPPP
	Integer  {  FFFF:0000:IIII:IIII

Notice that 64 bit pointers only take up 44 bit, leaving the top 20 bit unused. The new symbolic variant points to a union of the raw value and a pointer to the symbolic representation of it.