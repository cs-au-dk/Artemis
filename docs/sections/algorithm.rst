
Algorithm
=========

The algorithm below shows the major steps involved in the Artemis testing procedure. The finer details and capabilities are omitted from the algorithm itself, we refer to the detailed description of each step later in this document.

**Note**, this section is **incomplete** as we are evolving the testing procedure to accomedate new features.

.. code-block:: python

   def main(URL_initial, forms_initial):
                
       # Step 0: Global initialization
       worklist = Worklist()       
       browser = Browser()
       statistics = Statistics()
       input_strategy = InputStrategy()

       for configuration in worklist:

           # Step 1: Page load
           browser.reset_counters()
           browser.load_page(configuration.url)

           # Step 2: Post-load processing
           browser.fill_forms(forms_initial)
           
           # Step 3: Input sequence execution
           for input in configuration.inputs:
               browser.fill_forms(input.forms)    
               browser.trigger_event(input.event)

           # Step 4: Post-input processing
           statistics.update(browser.counters)

           # Step 5: Iteration
           configurations_new = input_strategy.generate(configuration, browser.counters, statistics)
           worklist.add(configurations_new)

Step 0: Global initialization
-----------------------------



Step 1: Page load
-----------------

Step 2: Post-load processing
----------------------------

Step 3: Input sequence execution
--------------------------------



Step 4: Postprocessing
----------------------



Step 5: Iteration
-----------------


