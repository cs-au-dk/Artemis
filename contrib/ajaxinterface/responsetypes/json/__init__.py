# -- encoding: utf-8 --

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

import simplejson

from structures import native_to_structure_class, Relation


class JsonType(object):
    def __init__(self, initial=None, rrpair=None):
        self._rrpairs = []

        if initial is not None:
            json = simplejson.loads(initial, strict=False)
            structure_class = native_to_structure_class(json)

            self._structure = structure_class(json)

        else:
            self._structure = None

        if rrpair is not None:
            self._rrpairs.append(rrpair)

    def get_relation_to(self, other_type):
        if self._structure is None:
            return Relation.supertype
        elif other_type.structure is None:
            return Relation.subtype
        else:
            return self.structure.get_relation_to(other_type.structure)

    def get_similarity_to(self, other_type):
        difference = self._structure.get_distance_to(other_type._structure)
        size = self._structure.get_distance_to(None) + \
               other_type._structure.get_distance_to(None)
        
        # print 'difference: %s, size: %s' % (difference, size) # debug
        
        similarity = float(size - difference) / size
        
        assert(0 <= similarity <= 1)
        
        return similarity

    def merge(self, other_type):
        self._rrpairs.extend(other_type._rrpairs)  
        self._structure = self._structure.merge(other_type._structure)

    @property
    def structure(self):
        return self._structure

    @property
    def rrpairs(self):
        return self._rrpairs
