#!/usr/bin/env python

import sys
import subprocess
import time
import re

STATS_START = '=== Statistics ==='
STATS_END = '=== Statistics END ==='
RE_STATS_LINE = re.compile(r'^(.*):(.*)$')


def run_artemis(address, iterations, tries=3):
    cmd = ['/usr/local/bin/artemis'] + ([address] if address[:3] != "http" else ['http://%s/' % address]) + [
        '-i %s' % iterations]
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
                    try:
                        value = int(match.group(2).strip().replace(" ", ""))
                    except ValueError:
                        value = match.group(2).strip()
                    report[key] = value
                except IndexError:
                    continue
        covered_lines = -1 if not 'WebKit::coverage::covered-unique' in report else report[
            'WebKit::coverage::covered-unique']
    except subprocess.CalledProcessError:
        covered_lines = -1
    end_t = time.time()
    return (end_t - start_t, covered_lines, 4-tries) if covered_lines > -1 or tries == 1 else run_artemis(address, iterations,
                                                                                                 tries=tries - 1)


def log_result_to_file(file_name, result):
    with open(file_name, 'a') as fp:
        fp.writelines("%s,%s\n" % (row[0], ",".join(",".join(str(ii) for ii in i) for i in row[1:])) for row in result)

    return file_name


def initialize_file(n):
    fn = 'result_file-%s.csv' % int(time.time())
    with open(fn, 'w') as fp:
        fp.write("Site,%s\n" % (
            ",".join("Num iterations #%s,Runtime #%s,Unique covered lines #%s, Tries #%s" % (i, i, i, i) for i in range(1, n + 1))))
    return fn


if __name__ == '__main__':
    if len(sys.argv) < 4:
        print 'Usage: %s <alexalist.csv> <top-n-sites> <num iterations>  <num iterations> ...  <num iterations> ' % \
              sys.argv[0]
        exit(1)
    site_list = sys.argv[1]
    top_n_sites = int(sys.argv[2])
    iterations = [int(i) for i in sys.argv[3:]]
    result = []
    fn = initialize_file(len(iterations))
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
            runs = []
            for it in iterations:
                print '%s iteration(s)' % it
                run = run_artemis(url, it)
                print 'Ran %s seconds with %s unique covered lines in %s attempt(s)' % run
                print ''
                runs.append([it] + list(run))
            result.append([url] + runs)
            log_result_to_file(fn, result)
            result = []
    print '=========================='
    print 'Run finished'
    print '=========================='
