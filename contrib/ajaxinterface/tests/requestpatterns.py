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

from ajaxinterface.raw.data import Request, RequestResponsePair
from ajaxinterface.ail.data import AilLine, AilSpecification

from ajaxinterface.requestpatterns.data import RequestPattern
from ajaxinterface.requestpatterns import split_or_merge_lines


class RequestPatternTest(unittest.TestCase):
    
    def test_get_actions(self):
        request = Request()
        request.method = 'GET'
        request.url = '/some/controller/page/?action=a1&pid=10'
        
        requestpattern = RequestPattern(request)
        
        self.assertEqual(requestpattern.args, [None, None, None])
        self.assertEqual(unicode(requestpattern),
                         '*/*/*?action=*&pid=*')
        
        match = Request()
        match.method = 'GET'
        match.url = '/some/controller/page/?action=a2&pid=11'
        
        changes = requestpattern.get_possible_changes(match)
        
        self.assertEqual(len(changes), 2)
        self.assertEqual(changes, [{'action': 'kwargs',
                                    'index': 'action'},
                                   {'action': 'kwargs',
                                    'index': 'pid'}])
        
        
class RequestPatternOperationsTest(unittest.TestCase):
    
    def _get_rrpair(self, *args, **kwargs):
        request = Request()
        request.method = 'GET'

        request.url = '/'.join(args)
        if len(kwargs) > 0:
            request.url += '?'
            request.url += '&'.join(['%s=%s' % (key,val) for key,val in kwargs.items()])
        
        rrpair = RequestResponsePair(None)
        rrpair.request = request
        
        return rrpair      
        
    def test_split_or_merge__merge(self):
        
        # setup 

        rrpair00 = self._get_rrpair('controller', action='a1', pid=12)
        rrpair0 = self._get_rrpair('controller', action='a1', pid=1)
        rrpair1 = self._get_rrpair('controller', action='a1', pid=108)
        
        rrpair2 = self._get_rrpair('controller', action='a1', pid=10)
        rrpair3 = self._get_rrpair('controller', action='a1', pid=121)
        
        line1 = AilLine()
        line1.sample_rrpairs = [rrpair1, rrpair0, rrpair00]
        line1.request_pattern = RequestPattern(rrpair1.request)
        
        line2 = AilLine()
        line2.sample_rrpairs = [rrpair2, rrpair3]
        
        ail_spec = AilSpecification()
        ail_spec.lines = [line1, line2]
        
        # test
        
        new_lines = split_or_merge_lines([line1, line2])
        
    def test_split_or_merge__merge_equal(self):
        
        # setup 

        rrpair1 = self._get_rrpair('controller', action='a1', pid=108)
        
        rrpair2 = self._get_rrpair('controller', action='a1', pid=108)
        
        line1 = AilLine()
        line1.sample_rrpairs = [rrpair1]
        line1.request_pattern = RequestPattern(rrpair1.request)
        
        line2 = AilLine()
        line2.sample_rrpairs = [rrpair2]
        
        ail_spec = AilSpecification()
        ail_spec.lines = [line1, line2]
        
        # test
        
        new_lines = split_or_merge_lines([line1, line2])
        
    def test_split_or_merge__split(self):
        
        # setup 

        rrpair00 = self._get_rrpair('controller', action='a1')
        rrpair0 = self._get_rrpair('controller', action='a2')
        rrpair1 = self._get_rrpair('controller', action='a1')
        
        rrpair2 = self._get_rrpair('controller', action='a3')
        rrpair3 = self._get_rrpair('controller', action='a3')
        
        rrpair4 = self._get_rrpair('controller', action='a4')
        rrpair5 = self._get_rrpair('controller', action='a4')
        
        line1 = AilLine()
        line1.sample_rrpairs = [rrpair00, rrpair0, rrpair1]
        line1.request_pattern = RequestPattern(rrpair1.request)
        
        line2 = AilLine()
        line2.sample_rrpairs = [rrpair2, rrpair3]
        
        line3 = AilLine()
        line3.sample_rrpairs = [rrpair4, rrpair5]
        
        ail_spec = AilSpecification()
        ail_spec.lines = [line1, line2, line3]
        
        # test
        
        new_lines = split_or_merge_lines([line1, line2]) 
        
        # other problems, split should both split the current line and insert
        # parts of other lines into the new line