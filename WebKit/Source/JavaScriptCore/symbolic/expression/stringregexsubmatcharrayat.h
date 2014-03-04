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

#ifndef SYMBOLIC_STRINGREGEXSUBMATCHARRAYAT_H
#define SYMBOLIC_STRINGREGEXSUBMATCHARRAYAT_H

#include <string>

#include "visitor.h"
#include "stringregexsubmatcharray.h"
#include "stringexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class StringRegexSubmatchArrayAt : public StringExpression
{
public:
    explicit StringRegexSubmatchArrayAt(StringRegexSubmatchArray* match, int group);
    void accept(Visitor* visitor);
    void accept(Visitor* visitor, void* arg);

	inline StringRegexSubmatchArray* getMatch() {
		return m_match;
	}
	inline int getGroup() {
		return m_group;
	}

private:
	StringRegexSubmatchArray* m_match;
	int m_group;

};
}

#endif
#endif // SYMBOLIC_STRINGREGEXSUBMATCHARRAYAT_H