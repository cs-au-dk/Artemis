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

#ifndef SYMBOLIC_STRINGBINARYOPERATION_H
#define SYMBOLIC_STRINGBINARYOPERATION_H

#include <string>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/runtime/UString.h"

#include "visitor.h"
#include "stringexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

typedef enum {
	CONCAT, STRING_EQ
} StringBinaryOp;

const char* opToString(StringBinaryOp op);


class StringBinaryOperation : public StringExpression
{
public:
    explicit StringBinaryOperation(StringExpression* lhs, StringBinaryOp op, StringExpression* rhs);
    void accept(Visitor* visitor);

	inline StringExpression* getLhs() {
		return m_lhs;
	}
	inline StringBinaryOp getOp() {
		return m_op;
	}
	inline StringExpression* getRhs() {
		return m_rhs;
	}

private:
	StringExpression* m_lhs;
	StringBinaryOp m_op;
	StringExpression* m_rhs;

};
}

#endif
#endif // SYMBOLIC_STRINGBINARYOPERATION_H