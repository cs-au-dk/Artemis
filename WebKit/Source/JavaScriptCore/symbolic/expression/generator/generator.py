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
protected:
    explicit %s() %s {}
};

}

#endif
""" % (ID, parent_inherit, ID, parent_init))

		fp.write("#endif // SYMBOLIC_%s_H" % ID.upper())

def generate_expression(target_dir, ID, parent, fields, enums):
	
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

""" % (', '.join(enum['values']), enum['ID']))

		fp.write("""
class %s : public %s
{
public:
    explicit %s(%s);
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

		fp.write("\nnamespace Symbolic\n");

		init = ',\n'.join(
			['    m_%s(%s)' % (field_name, field_name) for (field_type, field_name) in fields])

		fp.write("""
{

%s::%s(%s) :
    %s(),
%s
{
}
""" % (ID, ID, signature, parent, init))

		fp.write("""
}

#endif
""")

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

		print 'Add the following to your .pri file\n'

		for expression in expressions:

			print '    symbolic/expression/%s.h \\' % expression['ID'].lower()

		print ''

		for expression in expressions:

			if expression['type'] == 'expression':
				print '    symbolic/expression/%s.cpp \\' % expression['ID'].lower()
