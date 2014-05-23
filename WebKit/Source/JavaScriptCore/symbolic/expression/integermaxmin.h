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

#ifndef SYMBOLIC_INTEGERMAXMIN_H
#define SYMBOLIC_INTEGERMAXMIN_H

#include <string>

#include <list>

#include "visitor.h"
#include "integerexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class IntegerMaxMin : public IntegerExpression
{
public:
    explicit IntegerMaxMin(std::list<Expression*> expressions, bool max);
    void accept(Visitor* visitor);
    void accept(Visitor* visitor, void* arg);

	inline std::list<Expression*> getExpressions() {
		return m_expressions;
	}
	inline bool getMax() {
		return m_max;
	}

private:
	std::list<Expression*> m_expressions;
	bool m_max;

};
}

#endif
#endif // SYMBOLIC_INTEGERMAXMIN_H