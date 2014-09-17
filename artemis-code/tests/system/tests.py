#!/usr/bin/env python

import os
import unittest

from harness.environment import WebServer
from harness.artemis import execute_artemis

FIXTURE_ROOT = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'fixtures/')

class JQueryTest(unittest.TestCase):

	def test_detect_jquery_eventhandler(self):
		execute_artemis('test-jquery-live', '%s/jquery-live/index.html' % FIXTURE_ROOT)


class TimerTests(unittest.TestCase):

	def test_no_timers(self):
		report = execute_artemis('timer-no-timer', '%s/timers/notimer.html' % FIXTURE_ROOT)

		self.assertEqual(0, report.get('timers::registered', 0))

	def test_set_interval(self):
		report = execute_artemis('timer-set-interval', '%s/timers/timer.html' % FIXTURE_ROOT,
			input_strategy_same_length=0,
			iterations=2)

		self.assertEqual(2, report.get('timers::registered', 0))
		self.assertEqual(2, report.get('InputGenerator::added-configurations', 0))
		self.assertEqual(1, report.get('timers::fired', 0))

class InputGeneratorStrategies(unittest.TestCase):

	def test_form_input_constant(self):	

		report = execute_artemis('strategy-input-form-constant', 
			'%s/strategies/inputgeneration/form-input-constant.html' % FIXTURE_ROOT,
			strategy_form_input='javascript-constants',
			iterations=3)
		
		self.assertEqual(4, report.get('WebKit::coverage::covered-unique', 0));

class PrioritizationStrategies(unittest.TestCase):

	def test_coverage(self):
		report = execute_artemis('strategy-priority-coverage', 
			'%s/strategies/priority/coverage.html' % FIXTURE_ROOT,
			iterations=5,
			input_strategy_same_length=0,
			strategy_priority='constant')
		
		self.assertEqual(8, report.get('WebKit::coverage::covered-unique', 0));

		report = execute_artemis('strategy-priority-coverage', 
			'%s/strategies/priority/coverage.html' % FIXTURE_ROOT,
			iterations=5,
			strategy_priority='coverage')
		
		self.assertEqual(19, report.get('WebKit::coverage::covered-unique', 0));

	def test_readwrite(self):
		report = execute_artemis('strategy-priority-readwrite', 
			'%s/strategies/priority/readwrite.html' % FIXTURE_ROOT,
			iterations=4,
			strategy_priority='constant')
		
		self.assertEqual(6, report.get('WebKit::coverage::covered-unique', 0));

		report = execute_artemis('strategy-priority-readwrite', 
			'%s/strategies/priority/readwrite.html' % FIXTURE_ROOT,
			iterations=4,
			strategy_priority='readwrite')
		
		self.assertEqual(7, report.get('WebKit::coverage::covered-unique', 0));

#class NonTerminatingTests(unittest.TestCase):
#	
#	def test_non_terminating(self):
#		report = execute_artemis('nonterminating', '%s/nonterminating/nonterminating.html' % FIXTURE_ROOT)

class InstrumentationTests(unittest.TestCase):
	
	def test_alert(self):
		report = execute_artemis('instrumentation-alert', '%s/instrumentation/alert.html' % FIXTURE_ROOT)
		
		self.assertEqual(1, report.get('WebKit::alerts', 0));

	def test_jsconstants(self):	
		report = execute_artemis('instrumentation-jsconstants', '%s/instrumentation/jsconstants.html' % FIXTURE_ROOT,
			strategy_form_input='javascript-constants')
		
		self.assertEqual(2, report.get('WebKit::jsconstants', 0));

	def test_jsreadwrite(self):	
		report = execute_artemis('instrumentation-jsreadwrite', '%s/instrumentation/jsreadwrite.html' % FIXTURE_ROOT)
		
		self.assertEqual(3, report.get('WebKit::readproperties', 0));
		self.assertEqual(5, report.get('WebKit::writtenproperties', 0));

	def test_codecoverage(self):
		report = execute_artemis('instrumentation-codecoverage', '%s/instrumentation/codecoverage.html' % FIXTURE_ROOT)
		
		self.assertEqual(5, report.get('WebKit::coverage::covered', 0));

	def test_codecoverage_external(self):
		report = execute_artemis('instrumentation-codecoverage-external', '%s/instrumentation/codecoverage-external.html' % FIXTURE_ROOT)
		
		self.assertEqual(3, report.get('WebKit::coverage::covered', 0));

class AjaxTests(unittest.TestCase):
	
	def test_basic_sync_call_init(self):
		"""
		Detect possible ajax callback, but do not call it right now
		"""
		report = execute_artemis('ajax-basic-sync-call-init', '%s/ajax/index.html' % FIXTURE_ROOT,
								iterations=1)
		
		self.assertEqual(1, report.get('InputGenerator::added-configurations', 0));
		self.assertEqual(0, report.get("ajax::fired", 0));
		self.assertEqual(0, report.get('WebKit::alerts', 0));
		
	def test_basic_sync_call(self):
		"""
		Detect ajax call and call it in iteration 2
		"""
		report = execute_artemis('ajax-basic-sync-call', '%s/ajax/index.html' % FIXTURE_ROOT,
								 input_strategy_same_length=0,
								 iterations=2)
		
		self.assertEqual(2, report.get('InputGenerator::added-configurations', 0));
		self.assertEqual(1, report.get("ajax::fired", 0));
		self.assertEqual(2, report.get('WebKit::alerts', 0));

class FeatureSwitchTests(unittest.TestCase):

        def test_cvc4_feature_switch(self):

                key = 'Concolic::Solver::SuccessfulCoercionOptimisations'

                report = execute_artemis('test_cvc4_feature_switch', 
                                         '%sfeature-switches/cvc4-coercion-opt.html' % FIXTURE_ROOT,
                                         iterations=0,
                                         major_mode='concolic',
                                         concolic_event_sequences='simple',
                                         verbose=True)

                self.assertEqual(2, report.get(key, 0));

                report = execute_artemis('test_cvc4_feature_switch', 
                                         '%sfeature-switches/cvc4-coercion-opt.html' % FIXTURE_ROOT,
                                         iterations=0,
                                         major_mode='concolic',
                                         concolic_event_sequences='simple',
                                         concolic_disable_features='cvc4-coercion-opt',
                                         verbose=True)

                self.assertEqual(0, report.get(key, 0));

if __name__ == '__main__':
 	unittest.main()
