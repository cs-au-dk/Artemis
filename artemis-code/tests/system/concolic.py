#!/usr/bin/env python

import os

FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/concolic/')

import sys
import re
import unittest

from harness.artemis import execute_artemis, to_appropriate_type
from os import listdir
from os.path import isfile, join


class Concolic(unittest.TestCase):
    pass

def _list_tests_in_folder(folder):
    out = []

    for f in listdir(folder):
        p = join(folder, f)
        if not isfile(p) or f[0:1] == "_" or f[0:1] == "%" or not f[-5:] == '.html':
            continue
        result = {"test": {}, "i_test": {}, "fn": f}
        with open(p, 'r') as fl:
            if re.match("^\s*<!--\s*$", fl.readline()):
                for line in fl:
                    m = re.match("\s*TEST(_INTERN)? ([^<>!=\s]+)\s*((<|>|=|!)=?)([^=].*)$", line)
                    if not m:
                        continue
                    test_mode = "i_test" if m.group(1) else "test"
                    op = {"<": "lt", "<=": "leq", ">": "gt", ">=": "geq", "==": "eq", "=": "eq", "!": "neq",
                          "!=": "neq"}[m.group(3)]
                    if op not in result[test_mode]:
                        result[test_mode][op] = {}
                    result[test_mode][op][m.group(2).strip()] = m.group(5).strip()
                    if re.match("-->", line):
                        break

        if len(result['test']) == 0:
            result['test'] = None
        if len(result['i_test']) == 0:
            result['i_test'] = None
        out.append(result)
    return out

def _assert_test_case(test_case, op, v1, v2):
    if op == "eq":
        test_case.assertEqual(v1, v2)
    elif op == "neq":
        test_case.assertNotEqual(v1, v2)
    elif op == "geq":
        test_case.assertGreaterEqual(v1, v2)
    elif op == "gt":
        test_case.assertGreater(v1, v2)
    elif op == "leq":
        test_case.assertLessEqual(v1, v2)
    elif op == "lt":
        test_case.assertLess(v1, v2)

def _get_from_report(report, key):
    m = re.match('PC(\[([0-9]+)\])?', key)
    if m:
        index = int(m.group(2)) if m.group(2) else 0
        pc = report['pathCondition']
        assert len(pc) >= index + 1, "Not enough path conditions generated by artemis"
        return {"val": pc[index].replace(" ", ""), "pc": True}
    else:
        assert key in report, "Could not test for %s. Index not found in report" % key
        return {"val": report[key], "pc": False}


def test_generator(filename, name, test_dict=None, internal_test=None):
    def test(self):
        report = execute_artemis(name, "%s%s" % (FIXTURE_ROOT, filename),
                                 iterations=0,
                                 debug_concolic=' ',
                                 major_mode='concolic',
                                 concolic_event_sequences='simple',
                                 #concolic_search_procedure='dfs-testing',
                                 verbose=True)

        assert test_dict or internal_test, "No tests to execute"
        tested_unsat = False
        tested_not_written = False
        tested_not_solved = False
        tested_no_failed_injections = False

        if internal_test:
            for op, tMap in internal_test.iteritems():
                for s, v in tMap.iteritems():
                    tested_not_written = tested_not_written or s == "Concolic::Solver::ConstraintsNotWritten"
                    tested_unsat = tested_unsat or s == "Concolic::Solver::ConstraintsSolvedAsUNSAT"
                    tested_not_solved = tested_not_solved or s == "Concolic::Solver::ConstraintsNotSolved"
                    tested_no_failed_injections = tested_no_failed_injections or s == "Concolic::FailedInjections"
                    _assert_test_case(self, op, _get_from_report(report, s)['val'], _get_from_report(report, v)['val'])

        if test_dict:
            for op, tMap in test_dict.iteritems():
                for s, v in tMap.iteritems():
                    tested_not_written = tested_not_written or s == "Concolic::Solver::ConstraintsNotWritten"
                    tested_unsat = tested_unsat or s == "Concolic::Solver::ConstraintsSolvedAsUNSAT"
                    tested_not_solved = tested_not_solved or s == "Concolic::Solver::ConstraintsNotSolved"
                    tested_no_failed_injections = tested_no_failed_injections or s == "Concolic::FailedInjections"

                    v = to_appropriate_type(s, v)
                    r_val = _get_from_report(report, s)
                    _assert_test_case(self, op, r_val['val'], v.replace(" ", "") if r_val['pc'] else v)

        assert tested_unsat or not "Concolic::Solver::ConstraintsSolvedAsUNSAT" in report, \
            "Constraints solved as UNSAT are errors pr. default."
        assert tested_not_written or not "Concolic::Solver::ConstraintsNotWritten" in report, \
            "Not written constraints are pr. default an error"
        assert tested_not_solved or not "Concolic::Solver::ConstraintsNotSolved" in report, \
            "Not solved constraints are a pr. default an error."
        assert tested_no_failed_injections or not "Concolic::FailedInjections" in report, \
            "Failed injections are an error by default."

    return test


if __name__ == '__main__':

    for t in _list_tests_in_folder(FIXTURE_ROOT):
        test_name = 'test_%s' % t['fn'].replace(".", "_")
        test = test_generator(t['fn'], test_name, test_dict=t['test'], internal_test=t['i_test'])
        setattr(Concolic, test_name, test)

    unittest.main(buffer=True)

     
