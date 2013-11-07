#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/legacy-benchmarks/'
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


def assert_coverage_is_circa_expected(testCase, report, expected, linesOfCode, paperLinesOfCode, minMargin=0.1):
    covered = float(report.get("WebKit::coverage::covered-unique", -1)) / linesOfCode
    testCase.assertAlmostEqual(expected, covered,
                               delta=minMargin + (1-max(0, min(paperLinesOfCode / linesOfCode, 1))) * 0.1)


class HtmlEditTest(unittest.TestCase):
    url = '%s/htmledit/demo_full.html' % WEBSERVER_URL
    uuid = 'htmledit'
    loc = 734
    paperLoc = 568
    filesToExclude = ["%s/htmledit/htmlbox.min.js" % WEBSERVER_URL,
                      "%s/htmledit/htmlbox.undoredomanager.js" % WEBSERVER_URL,
                      "%s/htmledit/jquery-1.3.2.min.js" % WEBSERVER_URL]

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc, self.paperLoc)


class T3dModelTest(unittest.TestCase):
    url = '%s/3dmodel/index.html' % WEBSERVER_URL
    uuid = '3dmodel'
    loc = 492
    paperLoc = 393
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.74, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.74, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.74, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.74, self.loc, self.paperLoc)


class AjaxPollerTest(unittest.TestCase):
    url = '%s/ajax-poller/ajax-poller.php' % WEBSERVER_URL
    uuid = 'ajaxPoller'
    filesToExclude = []
    loc = 349
    paperLoc = 250

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.78, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.78, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.78, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.78, self.loc, self.paperLoc)


class AjaxTabsTest(unittest.TestCase):
    url = '%s/ajaxtabs/demo.htm' % WEBSERVER_URL
    uuid = 'ajaxTabs'
    loc = 208
    paperLoc = 156
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.88, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.88, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.89, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.89, self.loc, self.paperLoc)

class BallPoolTest(unittest.TestCase):
    url = '%s/ball_pool/index.html' % WEBSERVER_URL
    uuid = 'ballpool'
    loc = 327
    paperLoc = 256
    filesToExclude = ["%s/ball_pool/js/box2d.js" % WEBSERVER_URL,
                      "%s/ball_pool/js/protoclass.js" % WEBSERVER_URL]

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.89, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.89, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.90, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.90, self.loc, self.paperLoc)



class DragableBoxesTest(unittest.TestCase):
    url = '%s/dragable-boxes/dragable-boxes.html' % WEBSERVER_URL
    uuid = 'dragableBoxes'
    loc = 961
    paperLoc = 697
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.61, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.61, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc, self.paperLoc)


class DynamicArticlesTest(unittest.TestCase):
    url = '%s/dynamicArticles/index.html' % WEBSERVER_URL
    uuid = 'dynamicArticles'
    loc = 171
    paperLoc = 156
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.82, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.82, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.75, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.82, self.loc, self.paperLoc)


class FractalViewerTest(unittest.TestCase):
    url = '%s/fractal_viewer/index.html' % WEBSERVER_URL
    uuid = 'fractalViewer'
    loc = 1298
    paperLoc = 750
    filesToExclude = ['%s/fractal_viewer/js/lib/jquery-1.3.js' % WEBSERVER_URL]

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.63, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.75, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.75, self.loc, self.paperLoc)


class HomeostasisTest(unittest.TestCase):
    url = '%s/homeostasis/index.html' % WEBSERVER_URL
    uuid = 'homeostasis'
    loc = 3303
    paperLoc = 2037
    filesToExclude = []

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.62, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.63, self.loc, self.paperLoc)


class PacmanTest(unittest.TestCase):
    url = '%s/pacman/index.html' % WEBSERVER_URL
    uuid = 'pacman'
    loc = 3471
    paperLoc = 1857
    filesToExclude = ["%s/pacman/src/js/pacman10-hp.2.js" % WEBSERVER_URL,
                      "%s/pacman/src/js/pacman10-hp.js" % WEBSERVER_URL]

    def test_events_configuration(self):
        report = events_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc, self.paperLoc)

    def test_const_configuration(self):
        report = const_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc, self.paperLoc)

    def test_cov_configuration(self):
        report = cov_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc, self.paperLoc)

    def test_all_configuration(self):
        report = all_configuration_report(self.uuid, self.url, self.filesToExclude)
        assert_coverage_is_circa_expected(self, report, 0.44, self.loc, self.paperLoc)


if __name__ == '__main__':
    server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
    unittest.main()
    del server
