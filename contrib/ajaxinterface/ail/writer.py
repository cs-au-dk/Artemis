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
import re

from ajaxinterface.requestpatterns.data import wildcardify
from ajaxinterface.responsetypes.json import structures

LIMIT = 30

UNQUOTE_STRING = re.compile(r'^[a-zA-Z0-9_\-*\.\[\]]+$')


def _limit(value):
    try:
        value = unicode(value)
    except:
        value = '<unicode error>'

    if len(value) > LIMIT:
        return u'%s...' % value[:LIMIT]
    else:
        return value


def _quote(value):
    if UNQUOTE_STRING.match(value) is None:
        return '"%s"' % value
    else:
        return value

LINEWRAP = 80


def _linelength(*args):
    return sum([sum([len(value) for value in values]) for values in args])


def _write_request_pattern(request_pattern):
    assert(request_pattern is not None)

    kwargs = [u'%s:%s' % (key, _quote(_limit((wildcardify(value))))) for key,value in request_pattern.kwargs.iteritems()]
    args = [wildcardify(arg) for arg in request_pattern.args]

    if _linelength(args, kwargs) > LINEWRAP:
        kwarg_delimiter = u',\n\t'
    else:
        kwarg_delimiter = u', '

    return u'%s %s(%s)' % (request_pattern.request_method,
                         u'/'.join(args),
                         kwarg_delimiter.join(kwargs))

response_type_counter = 0


def _write_response_types(interface_path, basename, response_types):
    global response_type_counter

    files = []

    for response_type in response_types:
        filename = '%s.%s.json' % (basename, response_type_counter)
        
        response_type_counter += 1
        files.append('@%s' % filename)
        
        fp = open(os.path.join(interface_path, filename), 'w')
        write_schema(fp, response_type._structure, 0)
        fp.close()
    
    return '|'.join(files)


def write_to_file(interface_path, basename, ail_specification, debug=False):
    fp = open(os.path.join(interface_path, '%s.ail' % basename), 'w')

    try:
        rrpair = ail_specification.lines[0].sample_rrpairs[0]
        domain = '/'.join(rrpair.request.url.split('/')[:3])

        fp.write('URL %s\n\n' % domain)
    except IndexError:
        fp.write('URL \n\n')

    for line in ail_specification.lines:
        fp.write('%s : %s' % (_write_request_pattern(line.request_pattern),
                              _write_response_types(interface_path,
                                                    basename,
                                                    line.response_types)))

        if debug:
            fp.write('DEBUG')
            fp.write('Number of rrpairs : %s' % len(line.sample_rrpairs))

            for rrpair in line.sample_rrpairs:
                fp.write('\n%s' % rrpair.uuid)

        fp.write('\n\n')

    fp.close()


def _iprint(fp, text, ident, omit_newline=False):
    if ident != 0:
        fp.write('   ' * (ident-1))

    fp.write(text)
    
    if not omit_newline:
        fp.write('\n')


def _insert_optional(fp, _ident, optional):
    required = 'false' if optional else 'true'
    _iprint(fp, '"required": %s,' % required, _ident+1)


def write_schema(fp, structure, _ident, optional=False):
    if isinstance(structure, structures.AbstractPrimitiveType):
        _iprint(fp, '{', _ident)
        _insert_optional(fp, _ident, optional)
        _iprint(fp, '"type": "%s"' % structure.jlabel, _ident+1)
        _iprint(fp, '}', _ident, omit_newline=True)

    elif isinstance(structure, structures.UnionType):
        _iprint(fp, '{', _ident)
        _insert_optional(fp, _ident, optional)
        _iprint(fp, '"type": [', _ident+1)

        num_types = len(structure.types)
        for x in xrange(num_types):
            write_schema(fp, structure.types[x], _ident+2)
            
            if num_types == x+1:
                # the last element
                fp.write("\n")
            else:
                fp.write(",\n")

        _iprint(fp, ']', _ident+1)
        _iprint(fp, '}', _ident, omit_newline=True)

    elif isinstance(structure, structures.ArrayType):
        _iprint(fp, '{', _ident)
        _insert_optional(fp, _ident, optional)
        _iprint(fp, '"type": "array",', _ident+1)

        if structure.element_types is not None:
            _iprint(fp, '"items": [', _ident+1)

            num_types = len(structure.element_types)
            for x in xrange(num_types):
                write_schema(fp, structure.element_types[x], _ident+2)
                
                if num_types == x+1:
                    # last element
                    fp.write("\n")
                else:
                    fp.write(",\n")

            _iprint(fp, ']', _ident+1)

        else:
            _iprint(fp, '"items": []', _ident+1)

        _iprint(fp, '}', _ident, omit_newline=True)

    elif isinstance(structure, structures.ObjectType):
        # needs required

        _iprint(fp, '{', _ident)
        _insert_optional(fp, _ident, optional)
        _iprint(fp, '"type": "object",', _ident+1)
        _iprint(fp, '"properties": {', _ident+1)
        
        labels = list(structure._labels)
        num_labels = len(labels)
        
        for x in xrange(num_labels):
            _iprint(fp, '"%s": ' % labels[x], _ident+2)

            optional = False
            if labels[x] in structure._optional:
                optional = True
            
            write_schema(fp, structure._record[labels[x]], _ident+2, optional=optional)
            
            if num_labels == x+1:
                # last element
                fp.write("\n")
            else:
                fp.write(",\n")

        _iprint(fp, '}', _ident+1)
        _iprint(fp, '}', _ident, omit_newline=True)

    else:
        raise Exception("Unknown structure %s" % structure.__class__)