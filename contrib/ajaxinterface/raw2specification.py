#!/usr/bin/env python

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
import os

from raw.reader import RequestResponsePairFactory

from ajaxinterface import responsetypes
from ajaxinterface import requestpatterns

from ail.data import AilLine, AilSpecification
from ail.writer import write_to_file


def read_raw_data(raw_path):
    return RequestResponsePairFactory.get(raw_path)


def cluster_on_response(rrpairs):
    partial_ail_spec = AilSpecification()

    for response_type, rrpairs in responsetypes.cluster(rrpairs).items():
        line = AilLine()
        line.sample_rrpairs = rrpairs
        line.response_types = set([response_type])

        partial_ail_spec.lines.append(line)

    return partial_ail_spec


def cluster_on_request(partial_ail_spec):
    requestpatterns.refine_ail(partial_ail_spec)

    return partial_ail_spec


def merge_similar_types(partial_ail_spec, merge_threshold):
    """
    Merges similar responsetypes (JSONSchema specifications)
    """
    
    for line in partial_ail_spec.lines:
        #print 'line c = (%s)' % len(line.response_types) # debug
        line.response_types = responsetypes.merge_similar(line.response_types, merge_threshold)

    return partial_ail_spec


def run(raw_path, interface_path, basename):
    merge_threshold = 10

    rrpairs = read_raw_data(raw_path)

    # Data Clustering Phase
    ail_spec = cluster_on_response(rrpairs)
    ail_spec = cluster_on_request(ail_spec)

    # Pattern Generation Phase
    ail_spec = merge_similar_types(ail_spec, merge_threshold)
    write_to_file(interface_path, basename, ail_spec)

    return ail_spec

if __name__ == '__main__':
    try:
        raw_path, interface_path, basename = sys.argv[1:]
    except ValueError:
        print 'usage: raw2interface.py </path/to/raw> </path/to/interface> <basename>'
        print ''
        sys.exit(1)

    run(raw_path, interface_path, basename)
