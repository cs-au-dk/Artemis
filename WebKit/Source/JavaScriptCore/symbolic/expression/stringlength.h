/*
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

#ifndef SYMBOLIC_STRINGLENGTH_H
#define SYMBOLIC_STRINGLENGTH_H

#include <string>

#include "visitor.h"
#include "stringexpression.h"
#include "integerexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class StringLength : public IntegerExpression
{
public:
    explicit StringLength(StringExpression* string);
    void accept(Visitor* visitor);

	inline StringExpression* getString() {
		return m_string;
	}

private:
	StringExpression* m_string;

};
}

#endif
#endif // SYMBOLIC_STRINGLENGTH_H