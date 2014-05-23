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

#ifndef SYMBOLIC_INTEGERMAX_H
#define SYMBOLIC_INTEGERMAX_H

#include <string>

#include <list>

#include "visitor.h"
#include "integerexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class IntegerMax : public IntegerExpression
{
public:
    explicit IntegerMax(std::list<Expression*> expressions);
    void accept(Visitor* visitor);
    void accept(Visitor* visitor, void* arg);

	inline std::list<Expression*> getExpressions() {
		return m_expressions;
	}

private:
	std::list<Expression*> m_expressions;

};
}

#endif
#endif // SYMBOLIC_INTEGERMAX_H