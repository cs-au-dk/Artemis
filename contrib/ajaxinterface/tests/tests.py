"""
 Copyright 2013 Aarhus University

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
"""

import unittest
import os

from ajaxinterface import raw2specification

from requestpatterns import RequestPatternTest, RequestPatternOperationsTest
from responsetypes import ArrayStructureTest, MergingTest

DIRNAME = os.path.abspath(os.path.dirname(__file__))
BENCH_PATH = os.path.join(DIRNAME, 'fixtures')


class IntegrationTest(unittest.TestCase):

    def generic_test(self, name, raw_path=None, expect_number=None):
        if raw_path is None:
            raw_path = os.path.join(BENCH_PATH, name, 'manual')

        ail_spec = raw2specification.run(raw_path, '/tmp/', name)

        if expect_number is not None:
            self.assertEqual(len(ail_spec.lines), expect_number)
        else:
            self.assertNotEqual(len(ail_spec.lines), 0)

    def test_empty_example(self):
        self.generic_test('empty', expect_number=0)

    def test_simple_example(self):
        self.generic_test('simple')

    def test_empty_list_example(self):
        """
        We expect the empty list response and the list response
        to be merged and result in a single line.
        """
        self.generic_test('empty-list', expect_number=1)

    def test_buggenie(self):
        self.generic_test('buggenie')

    def test_elfinder(self):
        self.generic_test('elfinder')

    def test_eyeos(self):
        self.generic_test('eyeos')

    def test_impresspages(self):
        self.generic_test('impresspages')

    def test_kunagi(self):
        self.generic_test('kunagi')

    def test_simpleajax(self):
        self.generic_test('simpleajax')

    def test_tomatocart(self):
        self.generic_test('tomatocart')

if __name__ == '__main__':
    unittest.main()