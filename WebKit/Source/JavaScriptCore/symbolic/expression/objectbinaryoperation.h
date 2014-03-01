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

#ifndef SYMBOLIC_OBJECTBINARYOPERATION_H
#define SYMBOLIC_OBJECTBINARYOPERATION_H

#include <string>

#include "visitor.h"
#include "objectexpression.h"
#include "booleanexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

typedef enum {
	OBJ_EQ, OBJ_NEQ
} ObjectBinaryOp;

const char* opToString(ObjectBinaryOp op);
Type opGetType(ObjectBinaryOp op);


class ObjectBinaryOperation : public BooleanExpression
{
public:
    explicit ObjectBinaryOperation(ObjectExpression* lhs, ObjectBinaryOp op, ObjectExpression* rhs);
    void accept(Visitor* visitor);
    void accept(Visitor* visitor, void* arg);

	inline ObjectExpression* getLhs() {
		return m_lhs;
	}
	inline ObjectBinaryOp getOp() {
		return m_op;
	}
	inline ObjectExpression* getRhs() {
		return m_rhs;
	}

private:
	ObjectExpression* m_lhs;
	ObjectBinaryOp m_op;
	ObjectExpression* m_rhs;

};
}

#endif
#endif // SYMBOLIC_OBJECTBINARYOPERATION_H