.. _server-concolic-advice:

Server Mode - Concolic Advice
=============================

The server is able to record traces (sequences of actions) symbolically and provide suggestions for new form field
inputs to use with that sequence whihc will result in new JavaScript being executed.

The main server mode documentation is here: :ref:`server`.

Concolic Advice Model
---------------------

Each trace recorded is associated with a "sequence ID" identifying that particular action sequence.

The required calling sequence is:

* ``begintrace`` "MySequence"
    * There must be no trace already in progress.
* Some actions here, e.g. ``forminput``, ``click``, etc.
* ``endtrace`` "MySequence"
    * Sequence identifier must match the preceeding ``begintrace``.
* May record more traces, with any sequence identifiers.
    * If using the saem sequence identifier "MySequence" the same actions must be performed while recording.
* ``advice`` "MySequence"
    * Must have recorded at least one trace for "MySequence" already
    * Should not be called while recording a new trace.
* Any actions executed outside of a ``begintrace``/``endtrace`` block will not be recorded, for example actions to
    reset the state before re-running a new trace for the same sequence.

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
    
    **Errors:** If any trace is already in progress.
    
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
    
    
    **Errors:** If there is no trace in progress; if the in-progress trace used a different sequence ID.
    
* ``concolicadvice`` > ``advice``
    Request advice on form field values. There should not be a trace in-progress.
    
    The optional ``amount`` parameter (default value 1) requests that number of suggested form field assignments from
    the server. If there are less than this number available, all available advice will be returned. Setting ``amount``
    to 0 will return all available advice.
    
    N.B. It is meaningless but allowed to send the amount parameter with other ``concolicadvice`` actions as well.
    
    It is safe to call this command multiple times consecutively.
    
    Send::
    
        {
            "command": "concolicadvice",
            "action": "advice",
            "sequence": "MySequenceID",
            "amount": 3
        }
    
    Receive::
    
        {
            "concolicadvice": "done",
            "sequence": "MySequenceID",
            "values" : [
                [
                    {
                        "field": "//input[@id='input1']",
                        "value": "Hello"
                    },
                    {
                        "field": "//input[@id='input2']",
                        "value": "World"
                    }
                ],
                [
                    {
                        "field": "//input[@id='input1']",
                        "value": "Greetings"
                    },
                    {
                        "field": "//input[@id='input2']",
                        "value": "World"
                    }
                ],
                [
                    {
                        "field": "//input[@id='input1']",
                        "value": "Greetings"
                    },
                    {
                        "field": "//input[@id='input2']",
                        "value": "Everyone"
                    }
                ]
            ]
        }
    
    This example is a list of three separate suggested new traces. The first trace fills field ``input1`` with value
    "Hello" and field ``input2`` with value "World", and so on.
    
    If there is no more advice available for that sequence, then no values are returned::
    
        {
            "concolicadvice": "done",
            "sequence": "MySequenceID",
            "values" : []
        }
    
    N.B. This result is not necessarily final. If there are outstanding traces which have been suggested by Artemis
    but not yet executed then these may open up new possible explorations when they are executed.
    
    *Types:* The type of the suggested value can be either string, int or bool, depending on the field type.
    They follow the same rules as the ``forminput`` commnand.
    
    For example the response could be::
    
        {
            "concolicadvice": "done",
            "sequence": "MySequenceID",
            "values" : [
                [
                    {
                        "field": "//input[@id='my-text-box']",
                        "value": "Hello"
                    },
                    {
                        "field": "//input[@id='my-select-box']",
                        "value": "Hello"
                    },
                    {
                        "field": "//input[@id='my-select-box-accessed-by-index']",
                        "value": 1
                    },
                    {
                        "field": "//input[@id='my-check-box']",
                        "value": true
                    },
                    {
                        "field": "//input[@id='my-radio-button']",
                        "value": false
                    }
                ]
            ]
        }
    
    **Errors:** If there has not been any trace recorded with that id; if there is a trace in-progress.
    



