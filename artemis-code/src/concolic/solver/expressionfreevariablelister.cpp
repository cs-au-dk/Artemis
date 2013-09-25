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

#include "expressionfreevariablelister.h"

namespace artemis
{


void ExpressionFreeVariableLister::visit(Symbolic::SymbolicInteger* symbolicinteger)
{
    mResult.insert(QString(symbolicinteger->getSource().getIdentifier().c_str()), symbolicinteger->getSource().getIdentifierMethod());
}

void ExpressionFreeVariableLister::visit(Symbolic::ConstantInteger* constantinteger)
{
}

void ExpressionFreeVariableLister::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation)
{
    integerbinaryoperation->getLhs()->accept(this);
    integerbinaryoperation->getRhs()->accept(this);
}

void ExpressionFreeVariableLister::visit(Symbolic::IntegerCoercion* integercoercion)
{
    integercoercion->getExpression()->accept(this);
}

void ExpressionFreeVariableLister::visit(Symbolic::SymbolicString* symbolicstring)
{
    mResult.insert(QString(symbolicstring->getSource().getIdentifier().c_str()), symbolicstring->getSource().getIdentifierMethod());
}

void ExpressionFreeVariableLister::visit(Symbolic::ConstantString* constantstring)
{
}

void ExpressionFreeVariableLister::visit(Symbolic::StringBinaryOperation* stringbinaryoperation)
{
    stringbinaryoperation->getLhs()->accept(this);
    stringbinaryoperation->getRhs()->accept(this);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringRegexReplace* stringregexreplace)
{
    stringregexreplace->getSource()->accept(this);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringReplace* stringreplace)
{
    stringreplace->getSource()->accept(this);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringCoercion* stringcoercion)
{
    stringcoercion->getExpression()->accept(this);
}

void ExpressionFreeVariableLister::visit(Symbolic::SymbolicBoolean* symbolicboolean)
{
    mResult.insert(QString(symbolicboolean->getSource().getIdentifier().c_str()), symbolicboolean->getSource().getIdentifierMethod());
}

void ExpressionFreeVariableLister::visit(Symbolic::ConstantBoolean* constantboolean)
{
}

void ExpressionFreeVariableLister::visit(Symbolic::BooleanCoercion* booleancoercion)
{
    booleancoercion->getExpression()->accept(this);
}

void ExpressionFreeVariableLister::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation)
{
    booleanbinaryoperation->getLhs()->accept(this);
    booleanbinaryoperation->getRhs()->accept(this);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringLength* stringlength)
{
    stringlength->getString()->accept(this);
}


} // namespace artemis
