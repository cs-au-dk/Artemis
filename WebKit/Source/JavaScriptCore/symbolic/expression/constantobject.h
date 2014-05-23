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

#ifndef SYMBOLIC_CONSTANTOBJECT_H
#define SYMBOLIC_CONSTANTOBJECT_H

#include <string>

#include <list>

#include "visitor.h"
#include "objectexpression.h"

#ifdef ARTEMIS

namespace Symbolic
{

class ConstantObject : public ObjectExpression
{
public:
    explicit ConstantObject(bool isNull);
    void accept(Visitor* visitor);
    void accept(Visitor* visitor, void* arg);

	inline bool getIsnull() {
		return m_isNull;
	}

private:
	bool m_isNull;

};
}

#endif
#endif // SYMBOLIC_CONSTANTOBJECT_H