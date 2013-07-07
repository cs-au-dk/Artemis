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


def wildcardify(value):
    return value if value is not None else '*'


def get_change_value(request, change):
    args, kwargs = request.features
    
    if change['action'] == 'args':
        return args[change['index']]
    else:
        return kwargs[change['index']]


class RequestPattern(object):
    def __init__(self, sample_request):
        """
        Generate a "loose" request pattern
        
        E.g. /path/to/something/?key1=value1&key2=value2
        Is translated to /*/*/* key1=* key2=*
        """

        self.request_method = sample_request.method
        
        self.tight_args, self.tight_kwargs = sample_request.features
        self.args = []
        self.kwargs = {}
        
        for feature in self.tight_args:
            self.args.append(None)
            
        for key in self.tight_kwargs:
            self.kwargs[key] = None
   
    @property
    def signature(self):
        keys = self.kwargs.keys()
        keys.sort()
        keys.insert(0, len(self.args))
        
        return tuple(keys)
    
    @property
    def features(self):
        """
        Get a list of features used for referencing specific parts of the
        request pattern.
        """
        
        features = []
        
        for x in xrange(0, len(self.args)):
            features.append({'action': 'args',
                            'index': x})
            
        for key in self.kwargs:
            features.append({'action': 'kwargs',
                            'index': key})
                
        return features        
    
    def tighten_feature(self, feature):
        if feature['action'] == 'args':
            self.args[feature['index']] = self.tight_args[feature['index']]
        elif feature['action'] == 'kwargs':
            self.kwargs[feature['index']] = self.tight_kwargs[feature['index']]
        else:
            raise Exception("Unknown action")
   
    def __unicode__(self):
        kwargs = '&'.join(['%s=%s' % (key, wildcardify(value)) for key,value in self.kwargs.iteritems()])
        args = '/'.join([wildcardify(arg) for arg in self.args])
        
        if len(kwargs) > 0:
            return '%s?%s' % (args, kwargs)
        else:
            return args
   
    def includes(self, requests):
        if not hasattr(requests, '__iter__'):
            requests = [requests]
        
        for request in requests:
            if self.request_method != request.method:
                return False
            
            rrpair_args, rrpair_kwargs = request.features
            
            if len(rrpair_args) != len(self.args) or \
               len(rrpair_kwargs) != len(self.kwargs):
                return False
            
            for x in xrange(0, len(self.args)):
                if rrpair_args[x] != self.args[x] and \
                   self.args[x] is not None:
                    return False
                
            for key in self.kwargs:
                if not rrpair_kwargs.has_key(key):
                    return False
                
                if rrpair_kwargs[key] != self.kwargs[key] and \
                   self.kwargs[key] is not None:
                    return False
            
        return True
    
    def tighten(self, exclude_rrpair, include_rrpairs):
        """
        Tighten args and kwargs such that they don't include this particular
        rrpair
        """
        
        args, kwargs = exclude_rrpair.request.features
        
        if not self.includes(exclude_rrpair):
            return
        
        for x in xrange(0, len(self.args)):
            if self.args[x] is not None:
                continue
            
            self.args[x] = self.tight_args[x]
            
            if self.includes(exclude_rrpair) or \
               not self.includes(include_rrpairs):
                self.args[x] = None
                continue
            else:
                return
            
        for key in self.kwargs:
            if self.kwargs[key] is not None:
                continue
            
            self.kwargs[key] = self.tight_kwargs[key]
            
            if self.includes(exclude_rrpair):
                self.kwargs[key] = None
                continue
            else:
                return
        
        """ DEBUG   
        print self.args
        print self.kwargs
        
        print '\n\n tight \n\n'
        
        print self.tight_args
        print self.tight_kwargs
        
        print ''
        
        print rrpair.request.url
        print rrpair.uuid
        """
            
        raise Exception("Could not tighten request pattern")

    def get_possible_changes(self, sample_request):
        """
        Get a list of possible changes which would result in the request pattern
        not matching the sample.
        """
            
        if not self.includes(sample_request):
            return []
        
        args, kwargs = sample_request.features
        actions = []
        
        for x in xrange(0, len(self.args)):
            
            if self.args[x] is None and \
               args[x] != self.tight_args[x]:
                # args[x] is currently a wildcard, and the "tight" value is
                # different from the value of the rrpair we are trying not to 
                # match

                actions.append({'type': 'args',
                                'index': x})
            
        for key in self.kwargs:

            if self.kwargs[key] is None and \
               kwargs[key] != self.tight_kwargs[key]:
                # kwargs[key] is currently a wildcard, and the "tight" value is
                # different from the value of the rrpair we are trying not to 
                # match 
                
                actions.append({'action': 'kwargs',
                                'index': key})
                
        return actions
    
    def _set(self, change, value):
        if change['action'] == 'args':
            self.args[change['index']] = value
            return
        elif change['action'] == 'kwargs':
            self.kwargs[change['index']] = value
            return
        
        raise Exception("Change has unknown action %s" % change['action'])
    
    def _get_tight(self, change):
        if change['action'] == 'args':
            return self.tight_args[change['index']]
        elif change['action'] == 'kwargs':
            return self.tight_kwargs[change['index']] 
        
        raise Exception("Change has unknown action %s" % change['action'])
    
    def do(self, change):
        self._set(change, self._get_tight(change))
    
    def undo(self, change):
        self._set(change, None)
            