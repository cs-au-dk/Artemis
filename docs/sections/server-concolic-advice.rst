.. _server-concolic-advice:

Server Mode - Concolic Advice
=============================

The server is able to record traces (sequences of actions) symbolically and provide suggestions for new form field
inputs to use with that sequence whihc will result in new JavaScript being executed.

The main server mode documentation is here: :ref:`server`.

Concolic Advice Model
---------------------

Each trace recorded is associated with a "sequence ID" identifying that particular action sequence.


Commands
--------

* ``concolicadvice`` > ``begintrace``
    Begin recording a new trace (for a new or existing sequence). There must not be another trace in-progress.
    
    Send::
    
        {
            "command": "concolicadvice",
            "action": "begintrace",
            "sequence": "MySequenceID"
        }
    
    Receive::
    
        {
            "concolicadvice": "done"
        }
    
    The client can now send commands to execute actions (``forminput``, ``click``, etc.) which will be recorded into
    the trace and saved in the concolic tree for sequence "MySequenceID".
    
* ``concolicadvice`` > ``endtrace``
    End recording a trace. There must be a trace with the matching sequence ID in-proress.
    
    Send::
    
        {
            "command": "concolicadvice",
            "action": "endtrace",
            "sequence": "MySequenceID"
        }
    
    Receive::
    
        {
            "concolicadvice": "done"
        }
    
* ``concolicadvice`` > ``advice``
    Request advice on form field values. There should not be a trace in-progress.
    
    Send::
    
        {
            "command": "concolicadvice",
            "action": "advice",
            "sequence": "MySequenceID"
        }
    
    Receive::
    
        {
            "sequence": "MySequenceID",
            "values" : {
                "//input[@id='input1']": "Hello",
                "//input[@id='input2']": "World"
            }
        }
    
    If there is no more advice available for that sequence, then no values are returned::
    
        {
            "sequence": "MySequenceID",
            "values" : []
        }
    
    N.B. This result is not necessarily final. If there are outstanding traces which have been suggested by Artemis
    but not yet executed then these may open up new possible explorations when they are executed.
    



