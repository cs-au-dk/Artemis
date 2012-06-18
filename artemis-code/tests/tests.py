#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/'
WEBSERVER_URL = 'http://localhost:%s' % WEBSERVER_PORT

import unittest

from harness.environment import WebServer
from harness.artemis import execute_artemis

class JQueryTest(unittest.TestCase):

	def test_detect_jquery_eventhandler(self):
		execute_artemis('test-jquery-live', '%s/jquery-live/index.html' % WEBSERVER_URL)


class TimerTests(unittest.TestCase):

	def test_no_timers(self):
		report = execute_artemis('timer-no-timer', '%s/timers/notimer.html' % WEBSERVER_URL)

		self.assertEqual(0, report.get('timers::registered', 0))

	def test_set_interval(self):
		report = execute_artemis('timer-set-interval', '%s/timers/timer.html' % WEBSERVER_URL,
			iterations=2)

		self.assertEqual(2, report.get('timers::registered', 0))
		self.assertEqual(1, report.get('InputGenerator::added-configurations', 0))
		self.assertEqual(1, report.get('timers::fired', 0))

class NonTerminatingTests(unittest.TestCase):
	
	def test_non_terminating(self):
		report = execute_artemis('nonterminating', '%s/nonterminating/nonterminating.html' % WEBSERVER_URL)

if __name__ == '__main__':
	server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)
 	
 	unittest.main()

 	del server