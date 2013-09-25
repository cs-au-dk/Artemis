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

#ifdef ARTEMIS

#include "integerbinaryoperation.h"

namespace Symbolic
{

const char* opToString(IntegerBinaryOp op)
{
	static const char* OPStrings[] = {
        "+", "-", "*", "/", "==", "!=", "<=", "<", ">=", ">", "%", "!==", "==="
    };

    return OPStrings[op];
}

Type opGetType(IntegerBinaryOp op)
{
	static const Type types[] = {
	    INT, INT, INT, INT, BOOL, BOOL, BOOL, BOOL, BOOL, BOOL, INT, BOOL, BOOL
	};

	return types[op];
}


IntegerBinaryOperation::IntegerBinaryOperation(IntegerExpression* lhs, IntegerBinaryOp op, IntegerExpression* rhs) :
    IntegerExpression(),
    m_lhs(lhs),
    m_op(op),
    m_rhs(rhs)
{
}

void IntegerBinaryOperation::accept(Visitor* visitor) 
{
	visitor->visit(this); 	
}

}

#endif
