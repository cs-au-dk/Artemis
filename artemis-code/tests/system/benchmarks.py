#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/'
WEBSERVER_URL = 'http://localhost:%s' % WEBSERVER_PORT

import unittest

from harness.environment import WebServer
from harness.artemis import execute_artemis

def events_configuration_report(uuid, url, exclude):
    report = execute_artemis(uuid, url,
                             iterations=100,
                             strategy_form_input='random',
                             strategy_priority='constant',
                             exclude=exclude)
    return report


def const_configuration_report(uuid, url, exclude):
    report = execute_artemis(uuid, url,
                             iterations=100,
                             strategy_form_input='javascript-constants',
                             strategy_priority='constant',
                             exclude=exclude)
    return report


def cov_configuration_report(uuid, url, exclude):
    report = execute_artemis(uuid, url,
                             iterations=100,
                             strategy_form_input='javascript-constants',
                             strategy_priority='coverage',
                             exclude=exclude)
    return report


def all_configuration_report(uuid, url, exclude):
    report = execute_artemis(uuid, url,
                             iterations=100,
                             strategy_form_input='javascript-constants',
                             strategy_priority='all',
                             exclude=exclude)
    return report


def assert_coverage_is_circa_expected(testCase, report, expected, linesOfCode, margin=0.1):
    covered = float(report.get("WebKit::coverage::covered-unique", -1)) / linesOfCode
    testCase.assertAlmostEqual(expected, covered, delta=margin * expected)



class HtmlEditTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/htmledit/demo_full.html' % WEBSERVER_URL
    uuid = 'htmledit'
    loc = 568
    filesToExclude = ["%s/legacy-benchmarks/htmledit/htmlbox.min.js" % WEBSERVER_URL,
                      "%s/legacy-benchmarks/htmledit/htmlbox.undoredomanager.js" % WEBSERVER_URL,
                      "%s/legacy-benchmarks/htmledit/jquery-1.3.2.min.js" % WEBSERVER_URL]

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc)


class T3dModelTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/3dmodel/index.html' % WEBSERVER_URL
    uuid = '3dmodel'
    loc = 393
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.74, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.74, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.74, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.74, self.loc)


class AjaxPollerTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/ajax-poller/ajax-poller.php' % WEBSERVER_URL
    uuid = 'ajaxPoller'
    filesToExclude = []
    loc = 250

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.78, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.78, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.78, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.78, self.loc)


""" This tests fails on document load and should therefor be enabled once this bug has been fixed
class AjaxTabsTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/ajaxtabs/demo.htm' % WEBSERVER_URL
    uuid = 'ajaxTabs'
    loc = 156
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.88, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.88, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.89, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.89, self.loc)
"""

class BallPoolTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/ball_pool/index.html' % WEBSERVER_URL
    uuid = 'ballpool'
    loc = 256
    filesToExclude = ["%s/legacy-benchmarks/ball_pool/js/box2d.js" % WEBSERVER_URL,
                      "%s/legacy-benchmarks/ball_pool/js/protoclass.js" % WEBSERVER_URL]

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.89, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.89, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.90, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.90, self.loc)

class DragableBoxesTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/dragable-boxes/dragable-boxes.html' % WEBSERVER_URL
    uuid = 'dragableBoxes'
    loc = 697
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.61, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.61, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc)


class DynamicArticlesTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/dynamicArticles/index.html' % WEBSERVER_URL
    uuid = 'dynamicArticles'
    loc = 156
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.82, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.82, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.75, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.82, self.loc)


class FractalViewerTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/fractal_viewer/index.php' % WEBSERVER_URL
    uuid = 'fractalViewer'
    loc = 750
    filesToExclude = ['%s/legacy-benchmarks/fractal_viewer/js/lib/jquery-1.3.js' % WEBSERVER_URL]

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.63, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.75, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.75, self.loc)

class HomeostasisTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/homeostasis/index.html' % WEBSERVER_URL
    uuid = 'homeostasis'
    loc = 2037
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.63, self.loc)

class PacmanTest(unittest.TestCase):
    url = '%s/legacy-benchmarks/pacman/index.html' % WEBSERVER_URL
    uuid = 'pacman'
    loc = 1857
    filesToExclude = ["%s/legacy-benchmarks/pacman/src/js/pacman10-hp.2.js" % WEBSERVER_URL,
                      "%s/legacy-benchmarks/pacman/src/js/pacman10-hp.js" % WEBSERVER_URL]

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc)




if __name__ == '__main__':
    server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
    unittest.main()
    del server
