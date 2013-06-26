#!/usr/bin/env python

import sys
import subprocess
import time
import re

STATS_START = '=== Statistics ==='
STATS_END = '=== Statistics END ==='
RE_STATS_LINE = re.compile(r'^(.*):(.*)$')


def run_artemis(address, iterations):
    cmd = ['/usr/local/bin/artemis'] + ['http://%s/' % address] + ['-i %s' % iterations]
    start_t = time.time()
    try:
        std_out = (subprocess.check_output(cmd, stderr=subprocess.STDOUT)).decode("utf-8")
        statistics = std_out[std_out.find(STATS_START) + len(STATS_START):std_out.find(STATS_END)]
        report = {}
        for line in statistics.splitlines():
            match = RE_STATS_LINE.match(line)
            if match is not None:
                try:
                    key = match.group(1).strip()
                    value = int(match.group(2).strip())

                    report[key] = value
                except IndexError:
                    continue
        covered_lines = -1 if not 'WebKit::coverage::covered-unique' in report else report[
            'WebKit::coverage::covered-unique']
    except subprocess.CalledProcessError:
        covered_lines = -1
    end_t = time.time()
    return end_t - start_t, covered_lines


def save_result_to_file(result):
    fn = 'result_file-%s.csv' % int(time.time())
    with open(fn , 'w') as fp:
        fp.write("Site,Min Iteration,Max Iteration,Min Time,Max Time,Min Coverage,Max Coverage\n")
        fp.writelines(('%s,%s,%s,%s,%s,%s,%s\n' % (e[0], e[1][0], e[2][0], e[1][1], e[2][1], e[1][2], e[2][2])) for e in result)
    return fn

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print 'Usage: %s <alexalist.csv> <top-n-sites> <min-iterations[default=1]> <max-iterations[default=100]>' % \
              sys.argv[0]
        exit(1)
    site_list = sys.argv[1]
    top_n_sites = int(sys.argv[2])
    min_iteration = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    max_iteration = int(sys.argv[4]) if len(sys.argv) > 4 else 100
    result = []
    with open(site_list, 'r') as fp:
        for line in fp:
            if top_n_sites <= 0:
                break
            top_n_sites -= 1
            index, url = line.split(',')
            url = url.strip()
            print '=========================='
            print 'Visit %s' % url
            print '=========================='
            print ''
            print '%s iteration(s)' % min_iteration
            first_run = run_artemis(url, min_iteration)
            print 'Ran %s seconds with %s unique covered lines' % first_run
            print ''
            print '%s iteration(s)' % max_iteration
            second_run = run_artemis(url, max_iteration)
            print 'Ran %s seconds with %s unique covered lines' % second_run
            print ''
            result.append([url, [min_iteration] + list(first_run), [max_iteration] + list(second_run)])
    print '\n\n Saving result in %s \n' % save_result_to_file(result)
    print '=========================='
    print 'Run finished'
    print '=========================='
