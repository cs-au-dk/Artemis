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

#ifdef ARTEMIS

#include "stringbinaryoperation.h"

namespace Symbolic

{

StringBinaryOperation::StringBinaryOperation(StringExpression* lhs, StringBinaryOp op, StringExpression* rhs) :
    StringExpression(),
    m_lhs(lhs),
    m_op(op),
    m_rhs(rhs)
{
}

void StringBinaryOperation::accept(Visitor* visitor) 
{
	visitor->visit(this); 	
}

}

#endif
