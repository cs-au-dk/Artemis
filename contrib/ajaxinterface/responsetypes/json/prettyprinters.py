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


def iprint(text, ident):
    if ident != 0:
        print '   ' * (ident-1), text


def prettyprint_structure(node, ident=0):
    
    print unicode(node)


def prettyprint_type_hierarchy(node, ident=0):
    
    iprint('|- %s' % unicode(node), ident)
    
    for rrpair in node.rrpairs:
        iprint('|  %s' % rrpair.uuid, ident)
        
    iprint ('|--------------', ident)
    
    prettyprint_structure(node.structure, ident)
        
    print ''
        
    for subtype in node.subtypes:
        prettyprint_type_hierarchy(subtype, ident+1)