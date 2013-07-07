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

from json import JsonType, Relation


def _insert_into_typemap(rrpair, new_type, type_map):

    for json_type in type_map:
        relation = json_type.get_relation_to(new_type)

        if relation == Relation.equal:
            json_type.merge(new_type)
            type_map[json_type].append(rrpair)
            return True

    return False


def cluster(rrpairs):
    """
    Conducts high-level type inference on a set of request response pairs
    and clusters the rrpairs based on their types.

    Currently, this function discards all non-json data.

    Returns JsonType -> [RequestResponsePair]
    """

    type_map = {}

    for rrpair in rrpairs:
        if rrpair.is_valid() and rrpair.response.payload is not None:
            payload = rrpair.response.payload
            payload = payload.replace('//OK', '') # kunagi hack

            try:
                new_type = JsonType(payload, rrpair)

            except simplejson.decoder.JSONDecodeError:
                continue

            if not _insert_into_typemap(rrpair, new_type, type_map):
                type_map[new_type] = [rrpair]

    return type_map


def merge_similar(response_types, merge_threshold):

    pending = response_types.copy()

    while len(pending) > 0:
        candidate = pending.pop()
        
        closest_response_type = None
        closest_distance = None

        for response_type in pending:
            
            similarity = candidate.get_similarity_to(response_type)

            distance = 100 - similarity * 100
            
            if distance < merge_threshold and \
               (closest_distance is None or distance < closest_distance):
                closest_response_type = response_type
                closest_distance = distance

        if closest_response_type is not None and \
           closest_distance is not None:
            
            response_types.remove(candidate)
            closest_response_type.merge(candidate)

    return response_types

