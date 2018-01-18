import os
import shutil
import subprocess
import re
import codecs

ARTEMIS_EXEC = 'artemis'
OUTPUT_DIR = '.output'

STATS_START = '=== Statistics ==='
STATS_END = '=== Statistics END ==='

PATHCOND_START = '=== Last pathconditions ==='
PATHCOND_END = '=== Last pathconditions END ==='

RE_STATS_LINE = re.compile(r'^(.*):(.*)$')
RE_PATHCOND_LINE = re.compile(r'^PC\[([0-9]*)\]:(.+)$')
RE_ALERT_LINE = re.compile(r'^JAVASCRIPT ALERT:  "(.*)" $')


def execute_artemis(execution_uuid, url, iterations=1,
                    strategy_form_input=None,
                    strategy_priority=None,
                    strategy_target_selection=None,
                    coverage=None,
                    exclude=None,
                    string_fields=None,
                    boolean_fields=None,
                    integer_fields=None,
                    major_mode=None,
                    reverse_constraint_solver=False,
                    concolic_button=None,
                    dryrun=False,
                    verbose=False,
                    output_parent_dir=OUTPUT_DIR,
                    ignore_artemis_crash=False, # Suppresses the exception thrown by a non-zero return code and returns whatever information it can.
                    concolic_event_sequences=None,
                    concolic_search_procedure=None,
                    concolic_search_budget=None,
                    concolic_event_handler_report=False,
                    concolic_selection_procedure=None,
                    concolic_selection_budget=None,
                    verbosity=None,
                    sys_timeout=None,
                    event_visibility_check=None,
                    send_iteration_count=False,
                    event_delegation_testing=True,
                    concolic_test_mode_js=None,
                    event_filter_area=None,
                    extra_args=None, #TODO: Use kwargs instead.
                    **kwargs):
    output_dir = os.path.join(output_parent_dir, execution_uuid)

    if not dryrun:
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

    if strategy_target_selection is not None:
        args.append('--strategy-target-selection')
        args.append(strategy_target_selection)

    if coverage is not None:
        args.append('--coverage-report')
        args.append(coverage)
    
    if verbosity is not None:
        args.append('-v')
        args.append(verbosity)
    else:
        args.append('-v')
        args.append('all')

    if event_visibility_check is not None:
        args.append('--event-visibility-check')
        args.append("true" if event_visibility_check else "false")

    for key in kwargs:
        args.append('--%s' % key.replace('_', '-'))
        args.append(str(kwargs[key]))

    if exclude is not None:
        for file in exclude:
            args.append('--coverage-report-ignore')
            args.append(file)

    if string_fields is None:
        string_fields = []

    if boolean_fields is None:
        boolean_fields = []

    if integer_fields is None:
        integer_fields = []

    for field in string_fields:
        args.append('-f')
        args.append(field)

    for field in boolean_fields:
        args.append('-F')
        args.append(field)

    for field in integer_fields:
        args.append('-I')
        args.append(field)

    if reverse_constraint_solver:
        args.append('-e')

    if major_mode is not None:
        args.append('--major-mode')
        args.append(major_mode)

    if concolic_button is not None:
        args.append('--concolic-button')
        args.append(concolic_button)

    if concolic_event_sequences is not None:
        args.append('--concolic-event-sequences')
        args.append(concolic_event_sequences)

    if concolic_search_procedure is not None:
        args.append('--concolic-search-procedure')
        args.append(concolic_search_procedure)

    if concolic_search_budget is not None:
        args.append('--concolic-search-budget')
        args.append(concolic_search_budget)

    if concolic_event_handler_report:
        args.append('--concolic-event-handler-report')

    if concolic_selection_procedure is not None:
        args.append('--concolic-selection-procedure')
        args.append(concolic_selection_procedure)

    if concolic_selection_budget is not None:
        args.append('--concolic-selection-budget')
        args.append(concolic_selection_budget)

    if send_iteration_count:
        args.append('--testing-concolic-send-iteration-count-to-server')

    if event_delegation_testing:
        args.append('--event-delegation-testing')

    if concolic_test_mode_js is not None:
        args.append('--concolic-test-mode-js')
        args.append(concolic_test_mode_js)

    if event_filter_area is not None:
        args.append('--event-filter-area')
        args.append(event_filter_area)

    if extra_args is not None:
        args.extend(extra_args.split()) # TODO: In general split() is not good enough here.

    timeout = ['timeout', '%ss' % sys_timeout] if sys_timeout is not None else []

    cmd = timeout + [ARTEMIS_EXEC] + ([url] if url is not None else []) + args

    if dryrun or verbose:
        print(' '.join(cmd))

    if dryrun:
        return

    try:
        stdout = (subprocess.check_output(cmd, cwd=output_dir, stderr=subprocess.STDOUT)).decode("utf-8", "replace")
        returncode = 0
    except subprocess.CalledProcessError as e:
        if ignore_artemis_crash:
            stdout = e.output
            returncode = e.returncode
        else:
            #raise ArtemisCallException("Exception thrown by call %s \n\n %s \n\n Exception thrown by call %s" \
            #                % (e.cmd, e.output, e.cmd))
            raise ArtemisCallException("Exception thrown by call %s" % e.cmd)


    fp = codecs.open(os.path.join(output_dir, 'stdout.txt'), 'wb', encoding='utf-8')
    fp.write(stdout)
    fp.close()
    offset1 = stdout.find(STATS_START) + len(STATS_START)
    offset2 = stdout.find(STATS_END)
    statistics = stdout[offset1:offset2]

    report = {}
    report['returncode'] = returncode

    for line in statistics.splitlines():
        match = RE_STATS_LINE.match(line)

        if match is not None:
            try:
                key = match.group(1).strip()
                value = match.group(2).strip()

                value = to_appropriate_type(key, value)

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
    
    alert_calls = []
    for line in stdout.splitlines():
        match = RE_ALERT_LINE.match(line)
        if match is not None:
            value = match.group(1).strip()
            alert_calls.append(value)
    report["alerts"] = alert_calls
    
    return report


def to_appropriate_type(key, value):
    if value.isdigit() and ('INT_' in key or not 'SYM_IN_' in key):
        return int(value)

    if 'BOOL_' in key or not 'SYM_IN_' in key:
        if value == 'true':
            return True
        elif value == 'false':
            return False
    
    return value


class ArtemisCallException(Exception):
    pass
