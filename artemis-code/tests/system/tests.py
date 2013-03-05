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
		self.assertEqual(2, report.get('InputGenerator::added-configurations', 0))
		self.assertEqual(1, report.get('timers::fired', 0))

class InputGeneratorStrategies(unittest.TestCase):

	def test_form_input_constant(self):	

		report = execute_artemis('strategy-input-form-constant', 
			'%s/strategies/inputgeneration/form-input-constant.html' % WEBSERVER_URL,
			strategy_form_input='javascript-constants',
			iterations=2)
		
		self.assertEqual(4, report.get('WebKit::coverage::covered-unique', 0));

class PrioritizationStrategies(unittest.TestCase):

	def test_coverage(self):
		report = execute_artemis('strategy-priority-coverage', 
			'%s/strategies/priority/coverage.html' % WEBSERVER_URL,
			iterations=5,
			input_strategy_same_length=0,
			strategy_priority='constant')
		
		self.assertEqual(8, report.get('WebKit::coverage::covered-unique', 0));

		report = execute_artemis('strategy-priority-coverage', 
			'%s/strategies/priority/coverage.html' % WEBSERVER_URL,
			iterations=5,
			strategy_priority='coverage')
		
		self.assertEqual(19, report.get('WebKit::coverage::covered-unique', 0));

	def test_readwrite(self):
		report = execute_artemis('strategy-priority-readwrite', 
			'%s/strategies/priority/readwrite.html' % WEBSERVER_URL,
			iterations=4,
			strategy_priority='constant')
		
		self.assertEqual(6, report.get('WebKit::coverage::covered-unique', 0));

		report = execute_artemis('strategy-priority-readwrite', 
			'%s/strategies/priority/readwrite.html' % WEBSERVER_URL,
			iterations=4,
			strategy_priority='readwrite')
		
		self.assertEqual(7, report.get('WebKit::coverage::covered-unique', 0));

#class NonTerminatingTests(unittest.TestCase):
#	
#	def test_non_terminating(self):
#		report = execute_artemis('nonterminating', '%s/nonterminating/nonterminating.html' % WEBSERVER_URL)

class InstrumentationTests(unittest.TestCase):
	
	def test_alert(self):
		report = execute_artemis('instrumentation-alert', '%s/instrumentation/alert.html' % WEBSERVER_URL)
		
		self.assertEqual(1, report.get('WebKit::alerts', 0));

	def test_jsconstants(self):	
		report = execute_artemis('instrumentation-jsconstants', '%s/instrumentation/jsconstants.html' % WEBSERVER_URL)
		
		self.assertEqual(1, report.get('WebKit::jsconstants', 0));

	def test_jsreadwrite(self):	
		report = execute_artemis('instrumentation-jsreadwrite', '%s/instrumentation/jsreadwrite.html' % WEBSERVER_URL)
		
		self.assertEqual(3, report.get('WebKit::readproperties', 0));
		self.assertEqual(5, report.get('WebKit::writtenproperties', 0));

	def test_codecoverage(self):
		report = execute_artemis('instrumentation-codecoverage', '%s/instrumentation/codecoverage.html' % WEBSERVER_URL)
		
		self.assertEqual(5, report.get('WebKit::coverage::covered', 0));

	def test_codecoverage_external(self):
		report = execute_artemis('instrumentation-codecoverage-external', '%s/instrumentation/codecoverage-external.html' % WEBSERVER_URL)
		
		self.assertEqual(3, report.get('WebKit::coverage::covered', 0));

class AjaxTests(unittest.TestCase):
	
	def test_basic_sync_call_init(self):
		"""
		Detect possible ajax callback, but do not call it right now
		"""
		report = execute_artemis('ajax-basic-sync-call-init', '%s/ajax/index.html' % WEBSERVER_URL,
								iterations=1)
		
		self.assertEqual(1, report.get('InputGenerator::added-configurations', 0));
		self.assertEqual(0, report.get("ajax::fired", 0));
		self.assertEqual(0, report.get('WebKit::alerts', 0));
		
	def test_basic_sync_call(self):
		"""
		Detect ajax call and call it in iteration 2
		"""
		report = execute_artemis('ajax-basic-sync-call', '%s/ajax/index.html' % WEBSERVER_URL,
								iterations=2)
		
		self.assertEqual(1, report.get('InputGenerator::added-configurations', 0));
		self.assertEqual(1, report.get("ajax::fired", 0));
		self.assertEqual(1, report.get('WebKit::alerts', 0));

class LegacyBenchmarkTests(unittest.TestCase):

	def test_htmlbox(self):
		report = execute_artemis('legacybenchmark', '%s/legacy-benchmarks/htmledit/demo_full.html' % WEBSERVER_URL)


class t3dModelTest(unittest.TestCase):
	url = '%s/3dmodel/index.html' % WEBSERVER_URL;
	uuid = '3dmodel';
	loc = 393;
	margin = loc*0.1;
	def test_events_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='random',
			 strategy_priority='constant')
		self.assertLessEqual(0.74*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_const_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='constant')
		self.assertLessEqual(0.74*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_cov_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='coverage')
		self.assertLessEqual(0.74*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


	def test_all_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='all')
		self.assertLessEqual(0.74*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

class ajaxPollerTest(unittest.TestCase):
	url = '%s/ajax-poller/ajax-poller.php' % WEBSERVER_URL;
	uuid = 'ajaxPoller';
	loc = 250;
	margin = loc*0.1;

	def test_events_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='random',
			 strategy_priority='constant')
		loc = report.get("WebKit::coverage::number-of-loaded-lines",0);
		self.assertNotEqual(0,loc);
		self.assertLessEqual(0.78*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_const_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='constant')
		self.assertLessEqual(0.78*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_cov_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='coverage')
		self.assertLessEqual(0.78*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


	def test_all_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='all')
		self.assertLessEqual(0.78*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


class ajaxTabsTest(unittest.TestCase):
	url = '%s/ajaxtabs/demo.htm' % WEBSERVER_URL;
	uuid = 'ajaxTabs';
	loc = 156;
	margin = loc*0.1;
	def test_events_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='random',
			 strategy_priority='constant')
		self.assertLessEqual(0.88*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_const_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='constant')
		self.assertLessEqual(0.88*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_cov_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='coverage')
		self.assertLessEqual(0.89*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


	def test_all_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='all')
		self.assertLessEqual(0.89*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

class BallPoolTest(unittest.TestCase):
	url = '%s/ball_pool/index.html' % WEBSERVER_URL;
	uuid = 'ballpool';
	loc = 256;
	margin = loc*0.1;
	def test_events_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='random',
			 strategy_priority='constant')
		self.assertLessEqual(0.89*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_const_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='constant')
		self.assertLessEqual(0.89*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_cov_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='coverage')
		self.assertLessEqual(0.90*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


	def test_all_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='all')
		self.assertLessEqual(0.90*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

class dragableBoxesTest (unittest.TestCase):
	url = '%s/dragable-boxes/dragable-boxes.html' % WEBSERVER_URL;
	uuid = 'dragableBoxes';
	loc = 697;
	margin = loc*0.1;
	def test_events_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='random',
			 strategy_priority='constant')
		self.assertLessEqual(0.61*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_const_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='constant')
		self.assertLessEqual(0.61*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_cov_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='coverage')
		self.assertLessEqual(0.62*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


	def test_all_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='all')
		self.assertLessEqual(0.62*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


class dynamicArticlesTest (unittest.TestCase):
	url = '%s/dynamicArticles/index.html' % WEBSERVER_URL;
	uuid = 'dynamicArticles';
	loc = 156;
	margin = 156*0.1;
	def test_events_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='random',
			 strategy_priority='constant')
		self.assertLessEqual(0.82*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_const_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='constant')
		self.assertLessEqual(0.82*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_cov_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='coverage')
		self.assertLessEqual(0.75*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


	def test_all_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='all')
		self.assertLessEqual(0.82*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

class fractalViewerTest (unittest.TestCase):
	url = '%s/fractal_viewer/index.php' % WEBSERVER_URL;
	uuid = 'fractalViewer';
	loc = 750;
	margin = loc*0.1;
	def test_events_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='random',
			 strategy_priority='constant')
		self.assertLessEqual(0.62*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_const_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='constant')
		self.assertLessEqual(0.63*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));

		
	def test_cov_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='coverage')
		self.assertLessEqual(0.62*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


	def test_all_configuration (self):
		report = execute_artemis(self.uuid, self.url , 
		         iterations=100, 
			 strategy_form_input='javascript-constants',
			 strategy_priority='all')
		self.assertLessEqual(0.63*self.loc-self.margin,report.get("WebKit::coverage::covered-unique",0));


if __name__ == '__main__':
	server = WebServer(WEBSERVER_ROOT, WEBSERVER_PORT)

 	unittest.main()

 	del server
