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

#ifndef SYMBOLIC_INTEGERBINARYCOMPARISON_H
#define SYMBOLIC_INTEGERBINARYCOMPARISON_H

#include <string>

#include "integerexpression.h"
#include "negatableoperation.h"
#include "visitor.h"

#ifdef ARTEMIS

namespace Symbolic
{

typedef enum {
	INT_EQ, INT_NEQ, INT_LEQ, INT_GT, INT_GEQ, INT_LT, INT_SNEQ, INT_SEQ
} IntegerBinaryComparisonOp;

const char* opToString(IntegerBinaryComparisonOp op);
Type opGetType(IntegerBinaryComparisonOp op);


class IntegerBinaryComparison : public IntegerExpression, public NegatableOperation
{
public:
    explicit IntegerBinaryComparison(IntegerExpression* lhs, IntegerBinaryComparisonOp op, IntegerExpression* rhs);
    void accept(Visitor* visitor);

	inline IntegerExpression* getLhs() {
		return m_lhs;
	}
	inline IntegerBinaryComparisonOp getOp() {
		return m_op;
	}
	inline IntegerExpression* getRhs() {
		return m_rhs;
	}

private:
	IntegerExpression* m_lhs;
	IntegerBinaryComparisonOp m_op;
	IntegerExpression* m_rhs;

};
}

#endif
#endif // SYMBOLIC_INTEGERBINARYCOMPARISON_H