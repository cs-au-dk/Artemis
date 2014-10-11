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

#ifndef SYMBOLIC_SYMBOLICOBJECTPROPERTYSTRING_H
#define SYMBOLIC_SYMBOLICOBJECTPROPERTYSTRING_H

#include <string>

#include <list>

#include "visitor.h"
#include "stringexpression.h"
#include "symbolicobject.h"

#ifdef ARTEMIS

namespace Symbolic
{

class SymbolicObjectPropertyString : public StringExpression
{
public:
    explicit SymbolicObjectPropertyString(SymbolicObject* obj, std::string propertyName);
    void accept(Visitor* visitor);
    void accept(Visitor* visitor, void* arg);

	inline SymbolicObject* getObj() {
		return m_obj;
	}
	inline std::string getPropertyname() {
		return m_propertyName;
	}

private:
	SymbolicObject* m_obj;
	std::string m_propertyName;

};
}

#endif
#endif // SYMBOLIC_SYMBOLICOBJECTPROPERTYSTRING_H