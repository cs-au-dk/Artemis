#!/usr/bin/env python

WEBSERVER_PORT = 8001
WEBSERVER_ROOT = './fixtures/'
WEBSERVER_URL = 'http://localhost:%s' % WEBSERVER_PORT

import unittest

from harness.environment import WebServer
from harness.artemis import execute_artemis

class HtmlEditTest(unittest.TestCase):

	def test_htmlbox(self):
		report = execute_artemis('legacybenchmark', '%s/legacy-benchmarks/htmledit/demo_full.html' % WEBSERVER_URL)

class T3dModelTest(unittest.TestCase):
	url = '%s/legacy-benchmarks/3dmodel/index.html' % WEBSERVER_URL;
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

class AjaxPollerTest(unittest.TestCase):
	url = '%s/legacy-benchmarks/ajax-poller/ajax-poller.php' % WEBSERVER_URL;
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


class AjaxTabsTest(unittest.TestCase):
	url = '%s/legacy-benchmarks/ajaxtabs/demo.htm' % WEBSERVER_URL;
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
	url = '%s/legacy-benchmarks/ball_pool/index.html' % WEBSERVER_URL;
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

class DragableBoxesTest (unittest.TestCase):
	url = '%s/legacy-benchmarks/dragable-boxes/dragable-boxes.html' % WEBSERVER_URL;
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


class DynamicArticlesTest (unittest.TestCase):
	url = '%s/legacy-benchmarks/dynamicArticles/index.html' % WEBSERVER_URL;
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

class FractalViewerTest (unittest.TestCase):
	url = '%s/legacy-benchmarks/fractal_viewer/index.php' % WEBSERVER_URL;
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
