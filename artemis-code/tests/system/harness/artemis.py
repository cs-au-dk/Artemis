import os
import shutil
import subprocess
import re

ARTEMIS_EXEC = '/usr/local/bin/artemis'
OUTPUT_DIR = '.output'

STATS_START = '=== Statistics ==='
STATS_END = '=== Statistics END ==='

PATHCOND_START = '=== Last pathconditions ==='
PATHCOND_END = '=== Last pathconditions END ==='

RE_STATS_LINE = re.compile(r'^(.*):(.*)$')

RE_PATHCOND_LINE = re.compile(r'^PC\[([0-9]*)\]:(.+)$')


def execute_artemis(execution_uuid, url, iterations=1,
                    strategy_form_input=None,
                    strategy_priority=None,
                    coverage=None,
                    exclude=None,
                    fields=None,
                    major_mode=None,
                    reverse_constraint_solver=False,
                    dryrun=False,
                    **kwargs):
    output_dir = os.path.join(OUTPUT_DIR, execution_uuid)

    if os.path.isdir(output_dir):
        shutil.rmtree(output_dir)

    os.makedirs(output_dir)

    args = ["-i %s" % iterations]

    if strategy_form_input is not None:
        args.append('--strategy-form-input-generation')
        args.append(strategy_form_input)

    if strategy_priority is not None:
        args.append('--strategy-priority')
        args.append(strategy_priority)

    if coverage is not None:
        args.append('--coverage-report')
        args.append(coverage)

    for key in kwargs:
        args.append('--%s' % key.replace('_', '-'))
        args.append(str(kwargs[key]))

    if exclude is not None:
        for file in exclude:
            args.append('--coverage-report-ignore')
            args.append(file)

    if fields is None:
        fields = []

    for field in fields:
        args.append('-f')
        args.append(field)

    if reverse_constraint_solver:
        args.append('-e')

    if major_mode is not None:
        args.append('--major-mode')
        args.append(major_mode)

    cmd = [ARTEMIS_EXEC] + [url] + args

    if dryrun:
        print ' '.join(cmd)

    try:
        stdout = (subprocess.check_output(cmd, cwd=output_dir, stderr=subprocess.STDOUT)).decode("utf-8")

        fp = open(os.path.join(output_dir, 'stdout.txt'), 'wb')
        fp.write(stdout.encode())
        fp.close()
        offset1 = stdout.find(STATS_START) + len(STATS_START)
        offset2 = stdout.find(STATS_END)
        statistics = stdout[offset1:offset2]

        report = {}

        for line in statistics.splitlines():
            match = RE_STATS_LINE.match(line)

            if match is not None:
                try:
                    key = match.group(1).strip()

                    value = match.group(2).strip()

                    if value.isdigit():
                        value = int(value)

                    elif value == 'true':
                        value = True

                    elif value == 'false':
                        value = False

                    report[key] = value
                except:
                    print('Error parsing statistics result for line %s' % line)

        condOffset1 = stdout.find(PATHCOND_START) + len(PATHCOND_START)
        condOffset2 = stdout.find(PATHCOND_END)
        pathCond = stdout[condOffset1:condOffset2]
        pc = []
        for line in pathCond.splitlines():
            m = RE_PATHCOND_LINE.match(line)
            if m is not None:
                value = m.group(2).strip()
                pc.append(value)
        report['pathCondition'] = pc
        return report


    except subprocess.CalledProcessError as e:
        raise Exception("Exception thrown by call %s \n\n %s \n\n Exception thrown by call %s" \
                        % (e.cmd, e.output, e.cmd))
