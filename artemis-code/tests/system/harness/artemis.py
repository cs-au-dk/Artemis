
import os
import shutil
import subprocess
import re

ARTEMIS_EXEC = '/usr/local/bin/artemis'
OUTPUT_DIR = '.output'

STATS_START = '=== Statistics ==='
STATS_END = '=== Statistics END ==='

RE_STATS_LINE = re.compile(r'^(.*):(.*)$')

def execute_artemis(execution_uuid, url, iterations=1, 
    strategy_form_input=None,
    coverage=None):

    output_dir = os.path.join(OUTPUT_DIR, execution_uuid)

    if os.path.isdir(output_dir):
        shutil.rmtree(output_dir)
        
    os.makedirs(output_dir)
    
    args = []
    args.append("-i %s" % iterations)

    if strategy_form_input is not None:
        args.append('--strategy-form-input-generation')
        args.append(strategy_form_input)

    if coverage is not None:
        args.append('--coverage-report')
        args.append(coverage)

    cmd = [ARTEMIS_EXEC] + args + [url] 

    print cmd

    try:
	stdout = subprocess.check_output(cmd, cwd=output_dir, stderr=subprocess.STDOUT)

	fp = open(os.path.join(output_dir, 'stdout.txt'), 'w')
    	fp.write(stdout)
    	fp.close()

    	statistics = stdout[stdout.find(STATS_START)+len(STATS_START):stdout.find(STATS_END)]

    	report = {}

    	for line in statistics.splitlines():
            match = RE_STATS_LINE.match(line)

            if match is not None:
            	try:
                    key = match.group(1).strip()
                    value = int(match.group(2).strip())

                    report[key] = value
                except:
                    print 'Error parsing statistics result for line %s' % line

        return report

    except subprocess.CalledProcessError, e:
        raise Exception("Exception thrown by call %s \n\n %s \n\n Exception thrown by call %s" \
            % (e.cmd, e.output, e.cmd))
