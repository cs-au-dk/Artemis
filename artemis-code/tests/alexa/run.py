#!/usr/bin/env python

import sys
import subprocess
import shlex

if __name__ == '__main__':
    failures = []
    if len(sys.argv) < 4:
        print 'Usage: %s <alexalist.cvs> <top-x-sites> <iterations>' % sys.argv[0]
        exit(1)

    top_x_sites = int(sys.argv[2])
    iterations = int(sys.argv[3])

    success = 0
    failure = 0

    with open(sys.argv[1], 'r') as fp:
        for line in fp:

            if top_x_sites <= 0:
                break

            top_x_sites -= 1

            index, url = line.split(',')

            print '=========================='
            print 'Visit %s' % url
            print '=========================='
            print ''

            cmd = '/usr/local/bin/artemis http://%s/' % url

            process = subprocess.Popen(shlex.split(cmd))
            process.wait()

            print '=========================='

            if process.returncode == 0:
                print ' success'
                success += 1
            else:
                failures.append(url)
                print ' failed'
                failure += 1

                print '=========================='
                print ''

    print 'Statistics'
    print 'Success: %s' % success
    print 'Failure: %s' % failure
    if failure > 0:
        print 'Failed sites'
        for f in failures:
            print "  %s" % f
