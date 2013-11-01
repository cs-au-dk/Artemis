Artemis
=======

Copyright 2013 Aarhus University

Artemis is a tool that performs automated, feedback-directed testing
of JavaScript applications.

Contained in this repository is, besides the source for the tool, an
instrumented version of the WebKit code-base.

The tool is being developed by the [Center for Advanced Software Analysis](http://cs.au.dk/CASA/), at Aarhus University. For more information, see [brics.dk/artemis](http://brics.dk/artemis/)

Contributors
------------

The following people have contributed to the Artemis source code:

* Anders Møller
* Simon Holm Jensen
* Casper Svenning Jensen
* Kristoffer Just Andersen
* Christian Budde Christensen
* Ben Spencer

Included Software
-----------------

This software includes components from:

* WebKit (http://www.webkit.org/)
* Google Test (https://code.google.com/p/googletest/)
* Google Mock (https://code.google.com/p/googlemock/)
* Z3 (http://z3.codeplex.com/)
* Z3-str (http://www.cs.purdue.edu/homes/zheng16/str/)

Installation 
------------

See the included INSTALL file.

Usage
-----

For default settings simply write 

    artemis <url-to-be-tested>

in your terminal. This will test artemis against the given URL with four iterations and return statistics, such as number of covered lines,  in the terminal. 

Often you want to run Artemis for more than four iterations, this can be done by adding the `-i <number-of-interations>` option. 
As an example, running the following command

    artemis https://google.com -i 100 

will run Artemis on [google.com](http://google.com) for 100 iterations or until no more states can be visited. 

### Major modes
Artemis supports three different major modes for traversing websites: 

1. `artemis` *(default)*: Uses a feedback-directed approach as descriped in the [ICSE'11 Artemis paper](http://cs.au.dk/~amoeller/papers/artemis/paper.pdf).
2. `manual`: Opens a browser window for manual testing.  
3. `concolic`: Perform an automated concolic analysis of form validation code

The major mode can be chosen by setting the `--major-mode <mode>` option. As an example the following opens [google.com](https://google.com) in a browser window:

    artemis https://google.com --major-mode manual 

### Directing testing in Artemis
In major mode `artemis`, Artemis uses different heuristics in order to choose in which "direction" to test next: 
 
####Prioritization Functions

These functions are used to assign a priority to a given configuration in the worklist

 * `constant` *(default)*: Assigns a constant priority to every configuration, making the worklist work in a first-in-first-served manner. 
 * `random`: Assings a random priority to each configuration.
 * `coverage`: Will assign a higher priority to configurations that are known to result in a immediate larger coverage. This is done by looking at the transitive coverage of the eventhandlers. 
 * `readwrite`: Assigns a larger property to configurations which reads the most variables and properties previously written to.   

Setting the prioritization function can be done by the `--strategy-priority <strategy>` option. As an example the following command executes Artemis on [google.com](https://google.com) with the `readwrite` prioritization function and four iterations: 

    artemis https://google.com --strategy-priority readwrite



####Form input generators

In order to gain a larger code coverage Artemis generates input to forms instead of just submitting them with default values. Choosing the input is done by form input generators where the following generators are available:  

 * `random` *(default)*: This generator either generate a random string, random boolean or picks randomly between given options depending on the input type.  
 * `javascript-constants`: Here input are selected from previously encountered constants. 

The input generator can be set by setting the `--strategy-form-input-generation <strategy>` option. As an example the following command executes Artemis on [google.com](https://google.com) with the `javascript-constants` input generator, the `coverage` prioritization function and four iterations: 

    artemis https://google.com --staregy-form-input-generaton javascript-constants --strategy-priority coverage 

### Output

Artemis can generate different reports after end execution:

* *Coverage report*: This report contains detailed coverage information. The coverage report can be enabled by adding the `--coverage-report <report-type>` option. The coverage report can be generated either as a HTML-file or printed directly to `stdout` and files can be ignored from the reports by the `--coverage-report-ignore <URL>` option. 
* *Path-trace report*: This contains information of the execution path through the covered JavaScript code. The report is enabled by the `--path-trace-report <report-type>` option. The report is generated either to a HTML-file or printed directly to `stdout` just as the coverage report.  

Executing the following will generate a coverage report in the current folder, ignoring the external `jquery.min.js` and `stub.en.js` files

    artemis http://stackoverflow.com --coverage-report html 
            --coverage-report-ignore-url http://ajax.googleapis.com/ajax/libs/jquery/1.7.1/jquery.min.js  
            --coverage-report-ignore-url http://cdn.sstatic.net/Js/stub.en.js?v=f7b42019ec56 

###More infomation

Use the help command `artemis --help` for additional options.

Modifying the Software
----------------------

The developer documentation is available online (https://artemis.readthedocs.org).

To compile the documentation yourself you need to install sphinx (http://sphinx-doc.org/) and run the command ``make html`` or ``make latex`` in the ``docs/`` folder.
