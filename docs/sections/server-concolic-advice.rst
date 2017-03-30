.. _server-concolic-advice:

Server Mode - Concolic Advice
=============================

The server is able to record traces (sequences of actions) symbolically and provide suggestions for new form field
inputs to use with that sequence which will result in new JavaScript being executed.

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
    * If using the same sequence identifier "MySequence" the same actions must be performed while recording.
* ``advice`` "MySequence"
    * Must have recorded at least one trace for "MySequence" already
    * Should not be called while recording a new trace.
* Any actions executed outside of a ``begintrace``/``endtrace`` block will not be recorded, for example actions to
    reset the state before re-running a new trace for the same sequence.

N.B. There are some relaxations to this format allowed by specifically requesting them.
See the ``allowduringtrace`` option for ``concolicadvice`` and the ``implicitendtrace`` option for ``begintrace``.

Trace matching
~~~~~~~~~~~~~~

When traces are recorded for a certain sequence they are added to a tree of all execution paths for the execution in
that trace. The concolic advice makes suggestions for exploring new unseen branches in this tree.

In order to add new traces to the tree, they must have a prefix which matches the top of the tree. For example, if the
first trace has an initial action of filling field A, then all subsequent traces (for the same sequence ID) must begin
with filling field A. The simplest way to keep all new traces matching is to make sure **all traces recorded with the
same sequence ID should execute exactly the same actions during the trace recording**. The only thig which is safe to
change is the values injected into form fields.

In reality the requirement is slightly weaker. The prefix of the trace has to match the prefix of the tree until the
trace reaches a new unexplored area, after which there are no restrictions, other than matching with future traces.
For example, if selecting "Return" instead of "One-way" from a trip-planning form causes an extra "Return date" field
to be shown, it is safe to only fill "Return date" in the traces where "Return" has already been selected and ignore it
in the traces where "One-way" is selected. In practice it is difficult to know when this is safe without inspecting the
concolic tree so the above rule of always using identical traces is recommended.


Advice returned
~~~~~~~~~~~~~~~

The advice returned will contain suggested values for any form fields which were seen in any branch condition in
executed JavaScript code during the trace recording.

This means it may not include all the form fields which were filled during the trace - some of them will have no
validation and are considered "uninteresting" by our anlaysis.

It also means that values may be returned for form fields which were not in the original trace. A typical example of
this is if the trace contains only a submit button click, in which case it likely causes some form field validation
(leading to some contraints and so soe value suggestions) even though no field is filled. To excercise these branches
the client can either begin a new sequence which includes these fields, or arrange for the fields to have those values
set before beginning the [same] trace. In the latter case the analysis will not be able to see any per-field validation
for these fields which are set outside the trace, so some conditions may be missed.

Form restrictions
~~~~~~~~~~~~~~~~~

Radio buttons and select boxes (drop-down lists) have implied constraints.
If a select box only contains options "A", "B" and "C" then the concolic analysis will only return one of those strings
as a suggested value for that input.

In the particular case of select boxes we have some special support for dynamically changing forms.
A common pattern is to have two (or more) select boxes whose values update based on earlier selections.
For example if the fields are "Country" and "City" then selecting "UK" in the first will show a list of UK cities to
choose from in the second field. Selecting "Denmark" in the first field will give options of Danish cities, and so on.
In this case the analysis can see the updated values and will only make suggestions of valid pairs.
``{"Country": "UK", "City": "London"}`` would be valid but ``{"Country": "UK", "City": "Copenhagen"}`` would never be
returned as a suggestion.

Note that this pattern is only supported if the "Country" and "City" fields are both filled during the trace recording
and that no other types of dynamic form modifications are supported by the analysis.

The following tests from ``server.py`` and test pages show some examples of these types of forms:

* ``test_select_restrictions`` and ``concolic-select-restrictions.html``
* ``test_radio_restrictions`` and ``concolic-radio-restrictions.html``
* ``test_select_restrictions_dynamic`` and ``concolic-select-restrictions-dynamic.html``


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
    
    There is an optional boolean parameter ``implicitendtrace`` (default false) which allows this command to run even
    if there is already a trace in-progress. In this case the existing trace is ended (as if ``endtrace`` had been
    called) and the new trace is immediately started.
    
    **Errors:** If any trace is already in progress (unless ``implicitendtrace`` is set).
    
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
    
    There is also an option boolean parameter ``allowduringtrace`` (default false) which allows this command to be
    called while a trace is in-progress. The information gathered by an in-progress trace will not be available until
    ``endtrace`` is called, so calling ``advice`` during a trace does not gain anything. This means that if the first
    trace for "MySequenceID" is in-progress when advice is requested for "MySequenceID" then it will return an error
    because there is no concolic knowledge of that sequence yet.
    
    **Errors:** If there has not been any trace recorded with that id; if there is any trace in-progress (unless
    ``allowduringtrace`` is set).
    



