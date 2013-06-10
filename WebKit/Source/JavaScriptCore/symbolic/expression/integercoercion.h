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

#ifndef SYMBOLIC_INTEGERCOERCION_H
#define SYMBOLIC_INTEGERCOERCION_H

#include <string>

#include "visitor.h"
#include "expression.h"
#include "integerexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class IntegerCoercion : public IntegerExpression
{
public:
    explicit IntegerCoercion(Expression* expression);
    void accept(Visitor* visitor);

	inline Expression* getExpression() {
		return m_expression;
	}

private:
	Expression* m_expression;

};
}

#endif
#endif // SYMBOLIC_INTEGERCOERCION_H