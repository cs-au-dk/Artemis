/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

 // AUTO GENERATED - DO NOT MODIFY

#ifndef SYMBOLIC_STRINGINDEXOF_H
#define SYMBOLIC_STRINGINDEXOF_H

#include <string>

#include <list>

#include "integerexpression.h"
#include "stringexpression.h"
#include "visitor.h"

#ifdef ARTEMIS

namespace Symbolic
{

class StringIndexOf : public IntegerExpression
{
public:
    explicit StringIndexOf(StringExpression* source, StringExpression* pattern, IntegerExpression* offset);
    void accept(Visitor* visitor);
    void accept(Visitor* visitor, void* arg);

	inline StringExpression* getSource() {
		return m_source;
	}
	inline StringExpression* getPattern() {
		return m_pattern;
	}
	inline IntegerExpression* getOffset() {
		return m_offset;
	}

private:
	StringExpression* m_source;
	StringExpression* m_pattern;
	IntegerExpression* m_offset;

};
}

#endif
#endif // SYMBOLIC_STRINGINDEXOF_H