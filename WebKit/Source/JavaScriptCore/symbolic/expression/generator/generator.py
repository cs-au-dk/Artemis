#!/usr/bin/env python

import sys
import os
import simplejson

def field_filter_include(field):
	return field.replace('*', '').lower()

def generate_interface(target_dir, ID, parent):
	
	with open(os.path.join(target_dir, '%s.h' % ID.lower()), 'w') as fp:

		fp.write(
"""/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// AUTO GENERATED - DO NOT MODIFY

""")

		fp.write("#ifndef SYMBOLIC_%s_H\n" % ID.upper())
		fp.write("#define SYMBOLIC_%s_H\n\n" % ID.upper())

		fp.write("#ifdef ARTEMIS\n\n");

		dependencies = [parent] if parent is not None else []
		dependencies.append('visitor')

		for dependency in dependencies:
			fp.write("#include \"%s.h\"\n" % field_filter_include(dependency))

		parent_inherit = ''
		parent_init = ''

		if parent is not None:
			parent_inherit = ': public %s' % parent
			parent_init = ': %s()' % parent

		fp.write("""

namespace Symbolic
{

class %s %s
{
public:
    virtual void accept(Visitor* visitor) = 0;
};

}

#endif
""" % (ID, parent_inherit))

		fp.write("#endif // SYMBOLIC_%s_H" % ID.upper())

def generate_expression(target_dir, ID, parent, fields, enums):
	
	########### HEADER ##############

	signature = ', '.join(
		['%s %s' % (field_type, field_name) for (field_type, field_name) in fields])

	with open(os.path.join(target_dir, '%s.h' % ID.lower()), 'w') as fp:
		
		fp.write(
"""/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

 // AUTO GENERATED - DO NOT MODIFY

""")

		fp.write("#ifndef SYMBOLIC_%s_H\n" % ID.upper())
		fp.write("#define SYMBOLIC_%s_H\n\n" % ID.upper())

		fp.write("#include <string>\n\n")
		fp.write("#include \"JavaScriptCore/wtf/ExportMacros.h\"\n")
		fp.write("#include \"JavaScriptCore/runtime/UString.h\"\n\n")

		enum_ids = [enum['ID'] for enum in enums]

		dependencies = [field_type.replace('*', '') for (field_type, field_name) in fields \
			if not field_type.islower() and \
			field_type.replace('*', '') not in enum_ids and \
			'::' not in field_type]
		dependencies.append("visitor")
		dependencies.append(parent)

		for dependency in set(dependencies):
			fp.write("#include \"%s.h\"\n" % field_filter_include(dependency))

		fp.write("""
#ifdef ARTEMIS

namespace Symbolic
{
""")

		for enum in enums:
			fp.write("""
typedef enum {
	%s
} %s;

const char* opToString(%s op);

""" % (', '.join(enum['values']), enum['ID'], enum['ID']))

		fp.write("""
class %s : public %s
{
public:
    explicit %s(%s);
    void accept(Visitor* visitor);
""" % (ID, parent, ID, signature))

		for field_type, field_name in fields:
			fp.write("""
	inline %s get%s() {
		return m_%s;
	}""" % (field_type, field_name.capitalize(), field_name))

		fp.write("\n\nprivate:\n")

		for field_type, field_name in fields:
			fp.write("\t%s m_%s;\n" % (field_type, field_name))

		fp.write("""
};
}

#endif
""")

		fp.write("#endif // SYMBOLIC_%s_H" % ID.upper())

	############# Definitions ############

	with open(os.path.join(target_dir, '%s.cpp' % ID.lower()), 'w') as fp:

		fp.write(
"""/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

 // AUTO GENERATED - DO NOT MODIFY

""")
		
		fp.write("#ifdef ARTEMIS\n\n");

		dependencies = [ID]

		for dependency in dependencies:
			fp.write("#include \"%s.h\"\n" % field_filter_include(dependency))

		fp.write("\nnamespace Symbolic\n{\n");

		# enums

		for enum in enums:
			fp.write("""
const char* opToString(%s op)
{
	static const char* OPStrings[] = {
        %s
    };

    return OPStrings[op];
}

""" % (enum['ID'], ', '.join(['"%s"' % name for name in enum['names']])))

		# functions

		init = ',\n'.join(
			['    m_%s(%s)' % (field_name, field_name) for (field_type, field_name) in fields])

		fp.write("""
%s::%s(%s) :
    %s(),
%s
{
}
""" % (ID, ID, signature, parent, init))

		# visitor

		fp.write("""
void %s::accept(Visitor* visitor) 
{
	visitor->visit(this); 	
}
""" % ID)

		fp.write("""
}

#endif
""")

def generate_visitor(target_dir, object_IDs):

	############# VISITOR ###########

	with open(os.path.join(target_dir, 'visitor.h'), 'w') as fp:

		fp.write(
"""/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

 // AUTO GENERATED - DO NOT MODIFY

#ifdef ARTEMIS


#ifndef SYMBOLIC_VISITOR_H
#define SYMBOLIC_VISITOR_H

namespace Symbolic
{

""")

		for object_ID in object_IDs:

			fp.write("    class %s;\n" % object_ID)

		fp.write("""
class Visitor
{

public:
""")

		for object_ID in object_IDs:
			name = object_ID.lower()
			fp.write("    virtual void visit(%s* %s) = 0;\n" % (object_ID, name))


		fp.write("""
};

}

#endif
#endif
""")

def generate_index(target_dir, object_IDs):

	############# VISITOR ###########

	with open(os.path.join(target_dir, '..', 'expr.h'), 'w') as fp:

		fp.write(
"""/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

 // AUTO GENERATED - DO NOT MODIFY

#ifdef ARTEMIS

""")

		for object_ID in object_IDs:
			fp.write("#include \"expression/%s.h\"\n" % object_ID.lower())

		fp.write("#endif")

if __name__ == '__main__':

	if len(sys.argv) != 3:
		print 'Usage: %s <expressions file> <target dir>' % sys.argv[0]
		exit(1)

	source = sys.argv[1]
	target_dir = sys.argv[2]

	with open(source, 'r') as fp:

		expressions = simplejson.loads(fp.read())

		for expression in expressions:
			
			if expression['type'] == 'interface':
				generate_interface(
					target_dir,
					expression['ID'], 
					expression['parent'])

			else:
				fields = [(field_type, field_name) for (field_type, field_name) in expression['fields']]

				generate_expression(
					target_dir,
					expression['ID'],
					expression['parent'],
					fields,
					expression.get('enums', []))

		cexps = [expression['ID'] for expression in expressions \
					if expression['type'] == 'expression']

		generate_visitor(target_dir, cexps)
		generate_index(target_dir, cexps)

		print 'Add the following to your .pri file\n'

		for expression in expressions:

			print '    symbolic/expression/%s.h \\' % expression['ID'].lower()

		print '    symbolic/expression/visitor.h \\'
		print '    symbolic/expr.h'

		print ''

		for expression in expressions:

			if expression['type'] == 'expression':
				print '    symbolic/expression/%s.cpp \\' % expression['ID'].lower()

