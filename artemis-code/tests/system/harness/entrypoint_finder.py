"""
A utility for running our external entry-point finding tool.

In our case, we have a customised version of the DIADEM tool (http://diadem.cs.ox.ac.uk/) which can detect and return
the entry-points available at a given URL.
"""



def call_ep_finder(url, dry_run=False):
    """Returns a list of the XPath identifiers of buttons to be searched at the given URL."""
    
    # Write the URL to the input file used by DIADEM.
    
    # Run DIADEM.
    
    # Read the result file generated (make sure this file is saved in the testing directory for later analysis).
    
    # Return the list of EPs found.
    
    # TODO: dummy implementation (works on local tests)
    return ["//button", "//a"]
