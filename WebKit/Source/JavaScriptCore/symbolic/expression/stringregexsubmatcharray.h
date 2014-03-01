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

#ifndef SYMBOLIC_STRINGREGEXSUBMATCHARRAY_H
#define SYMBOLIC_STRINGREGEXSUBMATCHARRAY_H

#include <string>

#include "visitor.h"
#include "expression.h"
#include "stringexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class StringRegexSubmatchArray : public Expression
{
public:
    explicit StringRegexSubmatchArray(StringExpression* source, std::string* regexpattern);
    void accept(Visitor* visitor);
    void accept(Visitor* visitor, void* arg);

	inline StringExpression* getSource() {
		return m_source;
	}
	inline std::string* getRegexpattern() {
		return m_regexpattern;
	}

private:
	StringExpression* m_source;
	std::string* m_regexpattern;

};
}

#endif
#endif // SYMBOLIC_STRINGREGEXSUBMATCHARRAY_H