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

#include "expressionvalueprinter.h"

#ifdef ARTEMIS

namespace artemis
{

void ExpressionValuePrinter::visit(Symbolic::ConstantObject* obj, void* arg)
{
    m_result += obj->getIsnull() ? "null" : "not-null";
}

void ExpressionValuePrinter::visit(Symbolic::ConstantInteger* constantinteger, void* arg)
{
    std::ostringstream doubleStr;
    doubleStr << constantinteger->getValue();
    m_result += doubleStr.str();
}

void ExpressionValuePrinter::visit(Symbolic::ConstantString* constantstring, void* arg)
{
    m_result += '"';
    m_result += *(constantstring->getValue());
    m_result += '"';
}

void ExpressionValuePrinter::visit(Symbolic::ConstantBoolean* constantboolean, void* arg)
{
    m_result += constantboolean->getValue() ? "true" : "false";
}


// These names begin with SYM_IN_, so we don't need to mark them at all... it is clear what they are.

void ExpressionValuePrinter::visit(Symbolic::SymbolicInteger *symbolicinteger, void *arg)
{
    m_result += symbolicinteger->getSource().getIdentifier();
}

void ExpressionValuePrinter::visit(Symbolic::SymbolicString *symbolicstring, void* arg)
{
    m_result += symbolicstring->getSource().getIdentifier();
}

void ExpressionValuePrinter::visit(Symbolic::SymbolicBoolean *symbolicboolean, void *arg)
{
    m_result += symbolicboolean->getSource().getIdentifier();
}


}

#endif
