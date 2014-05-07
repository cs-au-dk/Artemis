
.. _webkit-instrumentation:

WebKit Instrumentation
======================

This section documents various modifications made to WebKit as part of our instrumentation.

Note, we require WebKit and specifically the JavaScript Core interpreter to be compiled in a non-JIT mode and in 64bit-mode (read: we do not support JIT compiling and the 32bit compatible version of WebKit).


Tracking Values Symbolically
----------------------------

WebKit has been extended with *symbolic values and semantics* mirroring the concrete values and semantics respectively. Symbolic values are injected at predetermined sources (currently only the value property on input element DOM objects). 

As an example, accessing the value property on DOM node D returns a concrete string, denoted C, marked as a symbolic value, denoted S, originating from D. Any concrete operation operation on C will be matched with a symbolic operation on S. Thus, if the length property is accessed on C it will return a concrete value C2 representing the concrete length of the string, and C2 will be marked with a symbolic value S2 representing the symbolic length of the symbolic string S.

We say that there exist a number of mutators in WebKit taking a number of inputs I_0 ... I_n and outputting an output value O. Artemis instruments WebKit such that in all mutators, the output value O is marked with a proper symbolic value taking into account the concrete semantics of the mutator and the concrete and symbolic values of the inputs.

The following diagram gives an overview of the different concrete values, mutators and symbolic values and how they relate in the implementation.

  .. image:: ../diagrams/valuesandmutators.png

Note, there exist three levels of concrete values in WebKit: JSValues, object interfaces and internal objects. The JSValues are used to represent both primitive values and pointers to objects in JavaScript. JSValue is the primary type being passed around in the JavaScript interpreter. If JSValue points to an object, then it has a pointer to an object interface. This interface acts as a proxy to internal objects, usually conducting type conversion while delegating business logic and storage of values to the internal objects. The object interfaces are automatically generated in order to allow different JavaScript interpreter implementations to interface with the same internal objects.

We have identified two primary mutators, the JavaScript interpreter and native functions. In general, the JavaScript interpreter only manipulates the primitive values stored in JSValue, while the native functions operate on everything from JSValue to the internal objects.

 * Symbolic values are attached to all primitive values stored in JSValue and the interpreter has been instrumented to maintain the symbolic values for all operations on JSValues. 
 * A **subset** of native functions operating on JSValues have been instrumented.
 * A **subset** of interface objects track symbolic values for their concrete properties (JSString and the value property on input elements).
 * A **subset** of native functions operating on interface/internal objects have been instrumented (JSString and input elements).

A note on strings: Symbolic strings are marked symbolic both in the JSValue pointing the the JSString object and in the JSString object itself. The JSValue will make sure to propagate its symbolic value to the JSString. The JSString is immutable so it will never change its own symbolic value, thus keeping the two consistent. The symbolic value needs to be represented in the JSString since the native functions operating on JSString never gets a reference to the enclosing JSValue (and these functions derive new symbolic values based on the current string, e.g. string length).

Symbolically Enhanced JavaScript Values
---------------------------------------

JavaScript values  in WebKit are NaN encoded 

NaN encoding is used in WebKit to represent JavaScript values, denoted ``JSValue``. Each ``JSValue`` is a 64bit value, either representing a *double*, *integer*, or a *pointer* to a ``JSCell``. A detailed description of this encoding can be found in ``JSValue.h``, `here <http://wingolog.org/archives/2011/05/18/value-representation-in-javascript-implementations>`_ `and here <http://en.wikipedia.org/wiki/X86-64#Virtual_address_space_details>`_.

We want to enhance each concrete JavaScript value with a pointer to a symbolic representation of the same value. Furthermore, we want this to be fairly efficient, and only decrease efficiency if a symbolic value is present.

If a concrete values is not associated with a symbolic value we use the current NaN encoding for performance.

We can't represent both a concrete value and a symbolic value within 64bit at the same time. In this case, we tag the value to be symbolic and store a pointer to an object in turn pointing to the concrete and the symbolic value.

Specifically, we change the following patterns::

 	Pointer   {  0000:PPPP:PPPP:PPPP
         	   / 0001:****:****:****
	Double    {         ...
         	   \ FFFE:****:****:****
	Integer   {  FFFF:0000:IIII:IIII

into::

  Pointer   {  0000:0PPP:PPPP:PPPP
             / 0001:****:****:****
  Double    {         ...
             \ FFFE:****:****:****
    
  Symbolic:
  Object    {  FFFF:3PPP:PPPP:PPPP
  True      {  FFFF:7PPP:PPPP:PPPP
  False	    {  FFFF:5PPP:PPPP:PPPP
  Null      {  FFFF:1PPP:PPPP:PPPP
  Double    {  FFFF:9PPP:PPPP:PPPP
  Integer   {  FFFF:DPPP:PPPP:PPPP
  Integer   {  FFFF:C000:IIII:IIII

Notice that 64bit pointers only take up 44bit, leaving the top 20bit unused.

We extend the value objects representation of 32 bit integers. Here, 4bit of the previously unused area for integers are used to tag a specific symbolic type, and the remaining bits are used for storing a pointer to a combined concrete and symbolic value.

Notice, that the bit patterns for the different symbolic values are as follows::

            a b c d
  Object    0 0 1 1
  Null      0 0 0 1
  True      0 1 1 1
  False     0 1 0 1
  S. Int    1 1 0 1
  S. Double 1 0 0 1
  Int       1 1 0 0 (not symbolic)

The (a) bit indicates if the value is numeric or not, the (d) bit indicates if the value is symbolic or not (in order to differentiate normal concrete integers).

Special Casing Symbolic Strings
-------------------------------

Strings are represented by a JSValue (object type) who points to a JSString. A string is made symbolic by marking both the JSValue and JSString as symbolic. It is not enough to only mark the JSValue as symbolic, because a number of internal library functions (which we need to instrument for correct symbolic handling) only operate on the JSString object, and can't access the JSValue pointing to it. We fix this by propagating the symbolic information from the JSValue to the JSString.

This can cause problems if two distinct JSValue objects point to the same JSString for optimization purposes. Some special handling exist to avoid this case.

Special Casing Symbolic Objects
-------------------------------

We do not support symbolic objects in general. However, we do mark specific objects as symbolic in order to implement symbolic handling of specific instances of objects.

 * We make the result returned by regexp operations (who return arrays or null) symbolic. The symbolic value from these operations is treated as a special null or non-null symbolic value, in order to reason about the outcome of a regexp match.
 
Special Casing Indirect Symbolic Values
---------------------------------------

 * We mark objects as indirect symbolic if they are accessed using a value lookup using a symbolic index. This is used as a flag in order to implement symbolic value properties on option elements within a select element soundly. See issue #82, access pattern 3.

