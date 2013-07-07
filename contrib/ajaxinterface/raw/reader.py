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


import os
import simplejson

from data import RequestResponsePair


class RequestResponsePairFactory(object):
    
    @staticmethod
    def read_request_headers(fp, rrpair):
        data = simplejson.loads(fp.read())
        
        rrpair.request.method = data['method']
        rrpair.request.url = data['url']
        rrpair.request.headers = simplejson.loads(data['headers'])
    
    @staticmethod
    def read_request_payload(fp, rrpair):
        rrpair.request.payload = fp.read()
    
    @staticmethod
    def read_response_headers(fp, rrpair):
        data = simplejson.loads(fp.read())
        
        rrpair.response.status_code = data['statusCode']
        rrpair.response.headers = simplejson.loads(data['headers'])
    
    @staticmethod
    def read_response_payload(fp, rrpair):
        rrpair.response.payload = fp.read()
    
    @staticmethod
    def decode_filename(fname):
        """
        Supported formats:
        
        Legacy
          <sequential number>-<timestamp>-<content type>-<response.json|payload[.extension]> |
          <sequential number>-<timestamp>-<request.json|request-payload.txt>
        New
          <uuid>.<request-headers|request-payload|response-headers|response-payload>[.extension]
          
        Since uuid contains a number of "-" characters, we can detect the format by counting the
        number of "-", if the amount is below 5 then it is the legacy format otherwise we try
        to use the new format.
        
        """

        legacy = fname.split('-')
        if len(legacy) < 5:
            uuid = '-'.join(legacy[:2])
            file_ext = None

            part1 = os.path.splitext(legacy[2])[0]
            part2 = os.path.splitext(legacy[3])[0] if len(legacy) == 4 else ''
            
            if part1 == 'request' and part2 == 'payload':
                file_content = 'request-payload'
            elif part1 == 'request':
                file_content = 'request-headers'
            elif part2 == 'response':
                file_content = 'response-headers'
            elif part2 == 'payload':
                file_content = 'response-payload'
            else:
                raise Exception('unknown file format for %s' % fname)
            
            return uuid, file_content, file_ext
        
        try:
            uuid, file_content, file_ext = fname.split('.', 2)
        except ValueError:
            uuid, file_content = fname.split('.', 1)
            file_ext = None
            
        return uuid, file_content, file_ext
        
    @classmethod
    def get(cls, search_path):
        """
        Returns a uuid -> rrpair dictionary
        """
        readers = {'request-headers': cls.read_request_headers,
                   'request-payload': cls.read_request_payload,
                   'response-headers': cls.read_response_headers,
                   'response-payload': cls.read_response_payload}
        
        rrpair_map = {}
        
        for step in os.walk(search_path):
            path, dirs, files = step
            
            if '.svn' in path.split('/'):
                continue
            
            for fname in files:
                file_path = os.path.join(path, fname)
                uuid, file_content, file_ext = cls.decode_filename(fname)
                
                fp = open(file_path, 'r')
                rrpair = rrpair_map.get(uuid, RequestResponsePair(uuid))
                rrpair.files.append(file_path)
                
                readers[file_content](fp, rrpair)
                
                rrpair_map[uuid] = rrpair
                fp.close()
            
        return rrpair_map.values()
            