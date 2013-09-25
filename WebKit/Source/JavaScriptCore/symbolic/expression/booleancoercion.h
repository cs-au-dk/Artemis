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

#ifndef SYMBOLIC_BOOLEANCOERCION_H
#define SYMBOLIC_BOOLEANCOERCION_H

#include <string>

#include "visitor.h"
#include "booleanexpression.h"
#include "expression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class BooleanCoercion : public BooleanExpression
{
public:
    explicit BooleanCoercion(Expression* expression);
    void accept(Visitor* visitor);

	inline Expression* getExpression() {
		return m_expression;
	}

private:
	Expression* m_expression;

};
}

#endif
#endif // SYMBOLIC_BOOLEANCOERCION_H