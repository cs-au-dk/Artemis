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

from ajaxinterface.responsetypes import Relation
from ajaxinterface.responsetypes.json.structures import ArrayType, StringType, \
     IntegerType, UnionType, ObjectType


class ArrayStructureTest(unittest.TestCase):

    def generic_array_test(self, a1_elements, a2_elements, target_relation):
        a1 = ArrayType(a1_elements)
        a2 = ArrayType(a2_elements)

        relation = a1.get_relation_to(a2)

        self.assertEqual(relation, target_relation)

    def test_relations_equal(self):
        self.generic_array_test([], [], Relation.equal)
        self.generic_array_test([3,3,3,4], [3], Relation.equal)

    def test_relations_subtype(self):
        self.generic_array_test([1], [], Relation.subtype)
        self.generic_array_test([1, 'string'], ['string'], Relation.subtype)
        self.generic_array_test([{'a': 1, 'b': 1}], [{'a': 1}], Relation.subtype)

    def test_relations_supertype(self):
        self.generic_array_test([], [1], Relation.supertype)
        self.generic_array_test(['string'], ['string', 2], Relation.supertype)


class MergingTest(unittest.TestCase):
    
    def test_primitives(self):
        p1 = StringType("string")
        p2 = IntegerType("integer")
        
        p0 = p1.merge(p2)
        
        self.assertTrue(isinstance(p0, UnionType))
        
    def test_objects(self):
        o1 = ObjectType({'prop1': "string",
                         'prop2': 12})
        
        o2 = ObjectType({'prop1': 12,
                         'prop2': "string"})    
    
        o0 = o1.merge(o2)
        
        self.assertTrue(isinstance(o0, ObjectType))
        self.assertEqual(len(o0._labels), 2)
        self.assertEqual(len(o0._optional), 0)
        
        self.assertTrue(isinstance(o0._record['prop1'], UnionType))
        self.assertTrue(isinstance(o0._record['prop2'], UnionType))

