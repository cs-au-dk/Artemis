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

import pprint
import urlparse
import cgi
from cStringIO import StringIO


class Request(object):
    
    def __init__(self):
        self.method = None
        self.url = None
        self.headers = None
        self.payload = None
        
        self._get_features = None
        self._post_features = None
        self._features = None
        
    @property
    def features(self):
        if self._features is None:
            
            gargs, gkwargs = self.get_features
            pargs, pkwargs = self.post_features
        
            kwargs = gkwargs.copy()
            
            for key, value in pkwargs.iteritems():
                try:
                    kwargs[key].extend(value)
                except KeyError:
                    kwargs[key] = value
            
            self._features = (gargs + pargs, kwargs)
        
        return self._features
        
    @property
    def get_features(self):
        if self._get_features is None:
            parts = urlparse.urlparse(self.url)
            
            args = parts.path.split('/')
            kwargs = urlparse.parse_qs(parts.query, keep_blank_values=True)
            
            # filter out "empty" args, a product of the split if the url ends
            # or starts with /
            args = filter(lambda x: x != '', args)
            
            self._remove_singlelist(kwargs)
            
            self._get_features = (args, kwargs)
            
        return self._get_features
    
    @property
    def post_features(self):     
        
        if self._post_features is None:
            
            kwargs = {}
            
            if not self.method == 'POST':
                kwargs = {}
            
            elif 'multipart/form-data' in self.headers.get('content-type', ''):
                content_type_params = {}
                for item in self.headers['content-type'].split(';')[1:]:
                    key,value = item.split('=')
                    content_type_params[key.strip()] = value.strip()
                    
                kwargs = cgi.parse_multipart(StringIO(self.payload), content_type_params)
            
            else:
                kwargs = urlparse.parse_qs(self.payload, keep_blank_values=True)
                
            self._remove_singlelist(kwargs)
            
            self._post_features = [], kwargs
            
        return self._post_features
        
    def is_valid(self):
        return self.method is not None and \
               self.url is not None and \
               self.headers is not None

    def _remove_singlelist(self, kwargs):
        for key in kwargs:
            if isinstance(kwargs[key], list) and '[]' not in key:
                kwargs[key] = kwargs[key][0] 

    def __unicode__(self):
        return \
"""
Request
*******

method: %s
url: %s

headers
-------

%s

payload
-------

%s
""" % (self.method,
       self.url,
       pprint.pformat(self.headers),
       pprint.pformat(self.payload))


class Response(object):
    
    def __init__(self):
        self.status_code = None
        self.headers = None
        self.payload = None

    @property
    def content_type_raw(self):
        return self.headers.get('content-type', '')\
               .split(';')[0]\
               .lower()
        
    def is_valid(self):
        return self.status_code is not None and \
               self.headers is not None and \
               type(self.headers) is dict

    def __unicode__(self):
        return \
"""
Response
********

status code: %s
content type: %s

headers
-------

%s

payload
-------

%s
""" % (self.status_code,
       self.content_type_raw,
       pprint.pformat(self.headers),
       pprint.pformat(self.payload))


class RequestResponsePair(object):
    
    def __init__(self, uuid):
        self.uuid = uuid
        self.request = Request()
        self.response = Response()
        self.files = []
        
    def is_valid(self):
        return self.request.is_valid() and \
               self.response.is_valid()
    
    def __unicode__(self):
        return '%s %s %s' % (self.request.method,
                             self.response.content_type_raw,
                             self.uuid)