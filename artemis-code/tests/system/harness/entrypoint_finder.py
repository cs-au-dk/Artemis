"""
A utility for running our external entry-point finding tool.

In our case, we have a customised version of the DIADEM tool (http://diadem.cs.ox.ac.uk/) which can detect and return
the entry-points available at a given URL.
"""

import os
import subprocess
import shutil
import csv


#TODO: Should this be set by an environment variable or something else?
EP_FINDER_DIR = '/home/ben/DIADEM/form.observer'
EP_FINDER_SCRIPT = 'form-observer.sh'
EP_FINDER_INPUT = 'form-observer-input.txt'
EP_FINDER_RESULT = 'buttons.csv'


def call_ep_finder(url, test_dir=".", dry_run=False):
    """Returns a list of the XPath identifiers of buttons to be searched at the given URL."""
    
    if dry_run:
        print os.path.join(EP_FINDER_DIR, EP_FINDER_SCRIPT)
        return
    
    # Write the URL to the input file used by DIADEM.
    with open(os.path.join(EP_FINDER_DIR, EP_FINDER_INPUT), 'w') as input_file:
        input_file.write(url + '\n')
    
    # Clear the result file in case we accidentally read an outdated version.
    try:
        os.remove(os.path.join(EP_FINDER_DIR, EP_FINDER_RESULT))
    except OSError:
        pass # If the file does not exist, ignore.
        # Note that this is not exactly what we want as OSError can be raised if the delete fails for another reason.
    
    # Run DIADEM (Save the output, even if it crashes or returns non-zero).
    cmd = os.path.join(EP_FINDER_DIR, EP_FINDER_SCRIPT)
    try:
        stdout = (subprocess.check_output(cmd, cwd=EP_FINDER_DIR, stderr=subprocess.STDOUT)).decode("utf-8")
        returncode = 0
    except subprocess.CalledProcessError as e:
        stdout = e.output
        returncode = e.returncode
    
    # Write the output to a log file.
    with open(os.path.join(test_dir, 'diadem-stdout.txt'), 'w') as stdout_file:
        stdout_file.write(stdout)
    
    # If there was a problem, raise an exception now that we have saved the output.
    if returncode != 0:
        raise DiademCallException("Exception thrown by call to DIADEM (returned %d)." % returncode)
    
    # Copy the result file to our test directory.
    shutil.copyfile(os.path.join(EP_FINDER_DIR, EP_FINDER_RESULT), os.path.join(test_dir, EP_FINDER_RESULT))
    
    # Read and return the list of EPs found.
    # The results file consists of one header row, and the two columns for the URL and the entry-point.
    results = []
    with open(os.path.join(test_dir, EP_FINDER_RESULT), 'rb') as result_file:
        csvreader = csv.reader(result_file)
        csvreader.next() # Skip header row.
        for row in csvreader:
            results.append(row[1])
    
    return results



class DiademCallException(Exception):
    pass
