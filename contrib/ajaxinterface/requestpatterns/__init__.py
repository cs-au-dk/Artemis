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


import itertools
from pprint import pprint

from ajaxinterface.ail.data import AilLine

from data import RequestPattern, get_change_value


def get_value_from_rrpair(rrpair, feature):
    args, kwargs = rrpair.request.features

    if feature['action'] == 'args':
        value = args[feature['index']]

    elif feature['action'] == 'kwargs':
        value = kwargs[feature['index']]

    else:
        raise Exception("Unknown action")
    
    if hasattr(value, '__iter__'):
        value = ','.join(value)
        
    return value


def _get_feature_cost(lines, features):

    observed_values = set()
    split_cost = 0
    merge_cost = 0

    for line in lines:

        values = set()
        
        for rrpair in line.sample_rrpairs:
            
            value = [get_value_from_rrpair(rrpair, feature) \
                     for feature in features]

            values.add(tuple(value))

        split_cost += len(values) - 1 # split x-1 times for x elements
        merge_cost += len(observed_values.intersection(values))

        observed_values = observed_values.union(values)

    cost = split_cost + merge_cost

    return cost, observed_values


def _do_split(lines, features):

    if features is None:
        features = []

    new_lines = {}

    for line in lines:
        for rrpair in line.sample_rrpairs:
            value = []
            
            for feature in features:
                value.append(get_value_from_rrpair(rrpair, feature))

            value = tuple(value)
            
            if not new_lines.has_key(value):
                new_lines[value] = AilLine()
                
            new_lines[value].sample_rrpairs.append(rrpair)
            new_lines[value].response_types.update(line.response_types)

    for value,line in new_lines.items():
        line.request_pattern = RequestPattern(line.sample_rrpairs[0].request)
        
        for feature in features:            
            line.request_pattern.tighten_feature(feature)

    return new_lines.values()

def is_constant_feature(lines, feature):
    """
    Constant features: a feature is constant if is always
    associates with a constant value. Don't generate permutations
    without these.
    """
    observed_value = None

    for line in lines:
        for rrpair in line.sample_rrpairs:
            value = get_value_from_rrpair(rrpair, feature)

            if observed_value is None:
                observed_value = value

            elif observed_value != value:
                return False

    return True

def split_or_merge_lines(lines):
    """
    Request pattern clustering

    Conducts splitting and merging on the given lines in order to construct a
    new set of lines in accordance with request pattern clustering.

    Returns [AilLine]
    """

    assert(len(lines) >= 2)

    #print 'Fixing conflict for %s lines' % len(lines) # debug

    features = []
    constant_features = []
    feature_sets = []
    
    for feature in lines[0].request_pattern.features:
        if is_constant_feature(lines, feature):
            constant_features.append(feature)
        else:
            features.append(feature)

    for i in xrange(len(features)):
        for selected_features in itertools.combinations(features, i+1):
            l = list(selected_features)
            l.extend(constant_features)
            feature_sets.append(tuple(l))

    min_values = None
    min_feature = None
    min_cost = None

    for feature_set in feature_sets:
        cost, value_pairs = _get_feature_cost(lines, feature_set)

        if min_cost is None or \
           cost < min_cost or \
           (cost == min_cost and len(feature_set) > len(min_feature)):
            min_cost = cost
            min_feature = feature_set
            min_values = value_pairs

    #print min_cost, min_feature, min_values, '<-- best'

    return _do_split(lines, min_feature)


def refine_ail(partial_ail_spec):
    queue = []
    queue.extend(partial_ail_spec.lines)

    while len(queue) > 0:
        line = queue.pop()

        # filter empty lines
        if len(line.sample_rrpairs) == 0:

            partial_ail_spec.lines.remove(line)
            continue

        line.request_pattern = RequestPattern(line.sample_rrpairs[0].request)

        # split line if the requests are disjoint
        # e.g. different number of arguments or differet request method
        matching = []
        nonmatching = []

        for rrpair in line.sample_rrpairs:
            if line.request_pattern.includes(rrpair.request):
                matching.append(rrpair)
            else:
                nonmatching.append(rrpair)

        if len(nonmatching) > 0:
            new_line = AilLine()
            new_line.response_types = line.response_types
            new_line.sample_rrpairs = nonmatching

            partial_ail_spec.lines.append(new_line)
            queue.append(new_line)

            line.sample_rrpairs = matching

    conflicting_lines = {}

    for line in partial_ail_spec.lines:
        signature = line.request_pattern.signature

        if not conflicting_lines.has_key(signature):
            conflicting_lines[signature] = []

        conflicting_lines[signature].append(line)

    for signature,lines in conflicting_lines.items():
        if len(lines) == 1:
            continue

        added, removed = split_or_merge_lines(lines), lines

        for line in removed:
            partial_ail_spec.lines.remove(line)

        for line in added:
            partial_ail_spec.lines.append(line)

    # make it pretty
    for line in partial_ail_spec.lines:
        for feature in line.request_pattern.features:
            values = set()
            for rrpair in line.sample_rrpairs:
                value = get_value_from_rrpair(rrpair, feature)
                values.add(value)

            if len(values) == 1:
                line.request_pattern.tighten_feature(feature)

    return partial_ail_spec
