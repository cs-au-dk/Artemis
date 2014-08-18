#!/usr/bin/env python

"""
A thin wrapper for calling concolic_real_sites.py multiple times with different sets of arguments to be passed to Artemis.
This allows "feature comparisons" to compare performance when using different options.
"""

import sys
import argparse
import subprocess
import getpass
import time
import datetime
import os



TEST_SUITE = os.path.join(os.environ['ARTEMISDIR'], 'artemis-code', 'tests', 'system', 'concolic_real_sites.py')


def main():
    print "Concolic test suite feature comparison."
    
    # Get the artemis options to be tested.
    parser = DefaultHelpParser(description="A wrapper for calling concolic_real_sites.py multiple times with different"
                                           "sets of arguments to be passed to Artemis.")
    parser.add_argument('csv_file', help="The CSV file listing the tests to be run. It contains three columns: unique "
                                         "site name, url, entry-point (XPath or 'auto'). The first row is a header.")
    parser.add_argument('options', nargs='+', help="A sequence of different option strings to be passed to the "
                                                   "calls to concolic_real_sites.py as 'extra-args'.")
    args = parser.parse_args()
    
    csv_file = args.csv_file
    options = args.options
    
    # Sanity check for the CSV file, in case they only supplied options...
    if not os.path.isfile(csv_file):
        print "Error, the CSV file doesn't seem to exist: \"%s\"" % csv_file
        sys.exit(1)
    
    # Set up the test directory
    test_run_id = time.strftime("%Y-%m-%d %H:%M:%S")
    test_dir = "Feature Comparison %s" % test_run_id
    os.mkdir(test_dir)
    
    # List options, and warn about the weird behaviour of extra_args in artemis.py, which naively splits the input.
    print
    print "Options to be tested:"
    for i, opt in enumerate(options, 1):
        opt_split = " ".join(["\"%s\"" % x for x in opt.split()])
        print "[%d] %s" % (i, opt_split)
    
    # Get the google login from the user.
    # We need this so it can be passed to each call of concolic_real_sites
    # TODO: Don't do this!
    print
    email = raw_input("Please enter your google account (email): ")
    password = getpass.getpass("Please enter your password: ")
    
    # Run the tests
    # TODO: They will clash if they are ever fast enough to have the same timestamp (e.g. the test results directory).
    print
    for i, opt in enumerate(options, 1):
        print "Running test suite %d" % i
        
        # TODO: Don't pass the password!
        cmd = [TEST_SUITE, os.path.abspath(csv_file), '-u', email, '-p', password, '--extra-args', opt]
        
        start_time = time.time()
        try:
            # Because of buffering of stdout and stderr the output can get a bit reordered.
            result = subprocess.check_output(cmd, cwd=test_dir, stderr=subprocess.STDOUT)
        except subprocess.CalledProcessError as e:
            # Ignore bad return codes.
            result = e.output
        end_time = time.time()
        
        print "    Time: %s" % datetime.timedelta(seconds=(end_time - start_time))
        
        test_file = os.path.join(test_dir, "test-output-%d.txt" % i)
        with open(test_file, 'w') as f:
            f.write(result)
        
    
    # Done all the tests.
    print
    print "Done."







# An argument parser which prints the help message after an error.
# http://stackoverflow.com/a/3637103/1044484
class DefaultHelpParser(argparse.ArgumentParser):
    def error(self, message):
        sys.stderr.write('Error: %s\n' % message)
        self.print_help()
        sys.exit(2)

if __name__ == "__main__":
    main()
