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

#ifndef SYMBOLIC_STRINGREGEXREPLACE_H
#define SYMBOLIC_STRINGREGEXREPLACE_H

#include <string>

#include "visitor.h"
#include "stringexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class StringRegexReplace : public StringExpression
{
public:
    explicit StringRegexReplace(StringExpression* source, std::string* regexpattern, std::string* replace);
    void accept(Visitor* visitor);

	inline StringExpression* getSource() {
		return m_source;
	}
	inline std::string* getRegexpattern() {
		return m_regexpattern;
	}
	inline std::string* getReplace() {
		return m_replace;
	}

private:
	StringExpression* m_source;
	std::string* m_regexpattern;
	std::string* m_replace;

};
}

#endif
#endif // SYMBOLIC_STRINGREGEXREPLACE_H