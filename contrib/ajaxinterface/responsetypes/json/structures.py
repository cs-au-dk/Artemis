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

import sys


def native_to_structure_class(native):
    """
    Get the json type related to a specific native type
    """

    if isinstance(native, dict):
        return ObjectType
    elif isinstance(native, list):
        return ArrayType
    elif isinstance(native, (str, unicode)):
        return StringType
    elif isinstance(native, bool):
        # important, check isinstance bool before
        # int, since isinstance(True, int) == True
        return BoolType
    elif isinstance(native, int):
        return IntegerType
    elif isinstance(native, float):
        return NumberType
    elif native is None:
        return NullType
    else:
        raise Exception()


class Relation:
    supertype = 1
    subtype = 2
    disjoint = 3
    equal = 4


class UnionType(object):
    def __init__(self, *args):
        self.types = list(args)

    def merge(self, other):
        if isinstance(other, UnionType):
            for other_type in other.types:
                match = False

                for t in self.types:
                    relation = other_type.get_relation_to(t)
                    if relation == Relation.equal:
                        match = True

                if match == False:
                    self.types.append(other_type)

            return self

        else:
            for t in self.types:
                relation = other.get_relation_to(t)

                if relation == Relation.equal:
                    return self

            self.types.append(other)
            return self

    def get_relation_to(self, other):
        raise NotImplementedError
    
    def _get_distance_to_asymmetric(self, typeset1, typeset2):
        distance = 0
        
        for t1 in typeset1:
            min_dist = sys.maxint
                        
            for t2 in typeset2:
                min_dist = min(min_dist, t1.get_distance_to(t2))
                            
            distance += min_dist
      
        return distance      
    
    def get_distance_to(self, other):
        """ 
        We want this function to be symmetric, so always compare
        unions such that the union with the lesser number of elements
        must be represented in the other union.
        """
        
        if other is None:
            distance = 0
            
            for t in self.types:
                distance = max(distance, t.get_distance_to(None))
                
            return distance
        
        if isinstance(other, UnionType):
             
            if len(self.types) < len(other.types):
                typeset1 = self.types
                typeset2 = other.types
            else:
                typeset1 = other.types
                typeset2 = self.types
                
        else:
            
            typeset1 = [other]
            typeset2 = self.types
            
        return self._get_distance_to_asymmetric(typeset1, typeset2)

    def __unicode__(self):
        types = ','.join([unicode(t) for t in self.types])
        return u'<union of %s>' % types


class AbstractPrimitiveType(object):

    def __init__(self, value):
        pass

    def merge(self, other):
        if isinstance(other, AbstractPrimitiveType) and other.t == self.t:
            return self
        elif isinstance(other, UnionType):
            return other.merge(self)
        else:
            return UnionType(self, other)

    def get_relation_to(self, other):
        if isinstance(other, AbstractPrimitiveType) and other.t == self.t:
            return Relation.equal
        else:
            return Relation.disjoint
        
    def get_distance_to(self, other):
        if other is None:
            return 1
        
        elif isinstance(other, AbstractPrimitiveType):
            if other.t == self.t:
                return 0
            else:
                return 2
        
        elif isinstance(other, UnionType):
            return other.get_distance_to(self)
        
        else:
            return 1 + other.get_distance_to(None)

    def __unicode__(self):
        return u'<primitive %s>' % type(self.t).__name__


class IntegerType(AbstractPrimitiveType):
    t = int
    jlabel = 'integer'


class StringType(AbstractPrimitiveType):
    t = str
    jlabel = 'string'


class BoolType(AbstractPrimitiveType):
    t = bool
    jlabel = 'boolean'


class NumberType(AbstractPrimitiveType):
    t = float
    jlabel = 'number'


class NullType(AbstractPrimitiveType):
    t = None
    jlabel = 'null'


class ArrayType(object):
    def __init__(self, values):
        self.element_types = None

        for value in values:
            json_type = native_to_structure_class(value)(value)

            if self.element_types is None:
                self.element_types = [json_type]
                continue

            match = False
            for element_type in self.element_types:
                relation = json_type.get_relation_to(element_type)

                if relation == Relation.equal:
                    match = True

            if match == False:
                self.element_types.append(json_type)

    def merge(self, other):
        if isinstance(other, ArrayType):
            
            if self.element_types is None:
                self.element_types = other.element_types
    
            elif other.element_types is None:
                pass
    
            else:
                for other_element in other.element_types:
                    matches = False
    
                    for element_type in self.element_types:
                        relation = other_element.get_relation_to(element_type)
    
                        if relation == Relation.equal:
                            matches = True
    
                    if not matches:
                        self.element_types.append(other_element)

            return self
        
        elif isinstance(other, UnionType):
            return other.merge(self)
        
        else:
            return UnionType(self, other)
    
    def _get_distance_to_asymmetric(self, array1, array2):
        distance = 0
        
        for t1 in array1.element_types:
            min_dist = sys.maxint
            
            for t2 in array2.element_types:
                min_dist = min(min_dist, t1.get_distance_to(t2))
                
            distance += min_dist
            
        return distance
    
    def get_distance_to(self, other):
        
        if other is None:
            distance = 0
            
            if self.element_types is not None:
                for t in self.element_types:
                    distance = max(distance, t.get_distance_to(None))
                
            return distance
            
        elif isinstance(other, AbstractPrimitiveType):
            return self.get_distance_to(None) + other.get_distance_to(None)
        
        elif isinstance(other, ObjectType):
            return self.get_distance_to(None) + other.get_distance_to(None)
        
        elif isinstance(other, UnionType):
            return other.get_distance_to(self)
        
        elif isinstance(other, ArrayType):
            if self.element_types is None or other.element_types is None:
                return 0
            
            if len(self.element_types) < len(other.element_types):
                array1 = self
                array2 = other
            else:
                array1 = other
                array2 = self
                
            return self._get_distance_to_asymmetric(array1, array2)

    def _has_equal_type_to_array(self, other):
        """
        Check if all elements of two arrays are equal.

        Assumes that the elements in one array are not equal internally.
        Thus, each element in A1 should find exactly one equal element
        in A2, and the number of elements in A1, A2, and equalities found
        should be equal.
        """

        equal_elements = set()

        for element_type in self.element_types:
            for other_element in other.element_types:
                relation = element_type.get_relation_to(other_element)

                if relation == Relation.equal:
                    equal_elements.add(other_element)

        return len(equal_elements) == len(self.element_types) and \
               len(equal_elements) == len(other.element_types)

    def _is_supertype_to_array(self, other):
        for element_type in self.element_types:
            found_match = False

            for other_element in other.element_types:
                relation = element_type.get_relation_to(other_element)

                if relation == Relation.equal or relation == Relation.supertype:
                    found_match = True

            if not found_match:
                return False

        return True

    def get_relation_to(self, other):
        """
        An array is a supertype of another array, if all elements in the array
        have equal type or is a supertype to at least one other element in
        the other array.

        An array is equal to another array, if all elements in the array are
        have an equal type to an element in the other array, and the other
        array does not contain any additional elements.

        An array is a subtype of another array, if the other array is a supertype
        to to that array.

        """

        if not isinstance(other, ArrayType):
            return Relation.disjoint

        if self.element_types is None and other.element_types is not None:
            return Relation.supertype

        if self.element_types is not None and other.element_types is None:
            return Relation.subtype

        if self.element_types is None and other.element_types is None:
            return Relation.equal

        if self._has_equal_type_to_array(other):
            return Relation.equal

        if self._is_supertype_to_array(other):
            return Relation.supertype

        if other._is_supertype_to_array(self):
            return Relation.subtype

        return Relation.disjoint

    def __unicode__(self):
        return u'[%s]' % u'|'.join(self.element_types)


class ObjectType(object):

    def __init__(self, initial):

        self._labels = set(initial.keys())
        self._record = {}
        self._optional = set()

        for key,value in initial.iteritems():
            self._record[key] = native_to_structure_class(value)(value)

    def merge(self, other):
        if isinstance(other, ObjectType):

            # update optional
            self._optional.update(self._labels.symmetric_difference(other._labels))
    
            # update record
    
            for label in self._labels.intersection(other._labels):
                self._record[label] = self._record[label].merge(other._record[label])
    
            for label in other._labels.difference(self._labels):
                self._record[label] = other._record[label]
    
            # update labels
            self._labels.update(other._labels)
    
            return self
        
        elif isinstance(other, UnionType):
            return other.merge(self)
        
        else:
            return UnionType(self, other)

    def get_relation_to(self, other):
        if not isinstance(other, ObjectType):
            return Relation.disjoint

        is_subtype = self._labels.issuperset(other._labels)
        is_supertype = self._labels.issubset(other._labels)

        if is_subtype or is_supertype:
            intersection = self._labels.intersection(other._labels)
            intersection_relations = set()

            for label in intersection:
                intersection_relations.add(
                    self._record[label].get_relation_to(other._record[label]))

            if is_subtype and is_supertype:
                """
                Case 1: is both subtype and supertype, indicating that the
                objects are equal. If we ignore labels which have equal
                types then we can observe the following cases
                a. All remaining labels are subtypes, then this is a subtype
                b. All remaining labels are supertypes, then this is a supertype
                c. All remaining labels are disjoint, then this is disjoint
                d. Mixed results, thus it is disjoint
                """

                try:
                    intersection_relations.remove(Relation.equal)
                except KeyError:
                    pass

                if len(intersection_relations) == 0:
                    return Relation.equal
                elif len(intersection_relations) == 1:
                    return intersection_relations.pop()
                else:
                    return Relation.disjoint

            elif is_subtype:
                """
                Case 2: is only subtype. Then we return it as a subtype if all
                labels are either equal or subtypes also.
                """

                if Relation.disjoint in intersection_relations or \
                   Relation.supertype in intersection_relations:
                    return Relation.disjoint

                else:
                    return Relation.subtype

            elif is_supertype:
                """
                Case 3: is only supertype. Then we return it as a supertype if all
                labels are either equal or supertypes also.
                """

                if Relation.disjoint in intersection_relations or \
                   Relation.subtype in intersection_relations:
                    return Relation.disjoint

                else:
                    return Relation.supertype


        return Relation.disjoint
    
    def get_distance_to(self, other):
        
        if other is None:
            distance = 0
            
            for label in self._labels:
                distance += 1
                distance += self._record[label].get_distance_to(None)
                
            return distance
        
        elif isinstance(other, AbstractPrimitiveType):
            return self.get_distance_to(None) + other.get_distance_to(None)
        
        elif isinstance(other, ArrayType):
            return self.get_distance_to(None) + other.get_distance_to(None)
        
        elif isinstance(other, UnionType):
            return other.get_distance_to(self)
        
        elif isinstance(other, ObjectType):
            distance = 0
            
            for label in self._labels.intersection(other._labels):
                distance += self._record[label].get_distance_to(other._record[label])
                
            for label in self._labels.difference(other._labels):
                distance += 1
                distance += self._record[label].get_distance_to(None)
                
            for label in other._labels.difference(self._labels):
                distance += 1
                distance += other._record[label].get_distance_to(None)
                
            return distance

    def __unicode__(self):
        uni = '{\n'

        for key,value in self._record.iteritems():
            uni += '%s: %s\n' % (key, unicode(value))

        uni += '}\n'
        return uni

