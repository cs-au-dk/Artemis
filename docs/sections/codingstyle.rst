
Coding Style Guidelines
=======================

The `QT coding style <http://qt-project.org/wiki/Qt_Coding_Style>`_ is used with the following additions:

Member variables
----------------

Member variables (private and public) are prefixed by ``m``.

Slots & Signals
---------------

Slots are prefixed by ``sl`` and signals ``sig``

Implicit or explicit this pointers
----------------------------------

Implicit this pointers are used when possible.

.. code-block:: c++

	void A::f()
	{
		this->mCount = 0; // wrong
		mCount = 0; // correct
	}

Memory management
-----------------

All memory management strategies `directly supported by QT <http://qt-project.org/wiki/ValueBasedAndPointerBasedTypes>`_ are accepted in addition to stack allocated objects ala. `RAII <http://en.wikipedia.org/wiki/RAII>`_. 

For user-defined types smart pointers (as in QSharedPointer) is highly encouraged.

If statements and brackets
--------------------------
	
Contrary to the QT coding style, brackets are always used with if statements even if the body of the if statement only consist of a single line. This is to improve robustness.

Whitespace for pointers and references
--------------------------------------

.. code-block:: c++

	// correct
	int* value;
	void* A::func(char* c) { ... 

	// wrong
	int *value;
	void *A::func(char *c) { ...