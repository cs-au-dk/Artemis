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

#ifndef SYMBOLIC_INTEGERBINARYOPERATION_H
#define SYMBOLIC_INTEGERBINARYOPERATION_H

#include <string>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/runtime/UString.h"

#include "integerexpression.h"
#include "visitor.h"

#ifdef ARTEMIS

namespace Symbolic
{

typedef enum {
	INT_ADD, INT_SUBTRACT, INT_MULTIPLY, INT_DIVIDE, INT_EQ, INT_NEQ, INT_LEQ, INT_LT, INT_GEQ, INT_GT, INT_MODULO, INT_SNEQ, INT_SEQ
} IntegerBinaryOp;


class IntegerBinaryOperation : public IntegerExpression
{
public:
    explicit IntegerBinaryOperation(IntegerExpression* lhs, IntegerBinaryOp op, IntegerExpression* rhs);
    void accept(Visitor* visitor);

	inline IntegerExpression* getLhs() {
		return m_lhs;
	}
	inline IntegerBinaryOp getOp() {
		return m_op;
	}
	inline IntegerExpression* getRhs() {
		return m_rhs;
	}

private:
	IntegerExpression* m_lhs;
	IntegerBinaryOp m_op;
	IntegerExpression* m_rhs;

};
}

#endif
#endif // SYMBOLIC_INTEGERBINARYOPERATION_H