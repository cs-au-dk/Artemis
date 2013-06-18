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

#ifndef SYMBOLIC_INTEGERBINARYARITHMETIC_H
#define SYMBOLIC_INTEGERBINARYARITHMETIC_H

#include <string>

#include "integerexpression.h"
#include "negatableoperation.h"
#include "visitor.h"

#ifdef ARTEMIS

namespace Symbolic
{

typedef enum {
	INT_ADD, INT_SUBTRACT, INT_MULTIPLY, INT_DIVIDE, INT_MODULO
} IntegerBinaryArithmeticOp;

const char* opToString(IntegerBinaryArithmeticOp op);
Type opGetType(IntegerBinaryArithmeticOp op);


class IntegerBinaryArithmetic : public IntegerExpression
{
public:
    explicit IntegerBinaryArithmetic(IntegerExpression* lhs, IntegerBinaryArithmeticOp op, IntegerExpression* rhs);
    void accept(Visitor* visitor);

	inline IntegerExpression* getLhs() {
		return m_lhs;
	}
	inline IntegerBinaryArithmeticOp getOp() {
		return m_op;
	}
	inline IntegerExpression* getRhs() {
		return m_rhs;
	}

private:
	IntegerExpression* m_lhs;
	IntegerBinaryArithmeticOp m_op;
	IntegerExpression* m_rhs;

};
}

#endif
#endif // SYMBOLIC_INTEGERBINARYARITHMETIC_H