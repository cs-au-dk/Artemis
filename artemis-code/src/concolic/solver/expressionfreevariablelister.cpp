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


void ExpressionFreeVariableLister::visit(Symbolic::ConstantObject* obj, void* arg)
{
}

void ExpressionFreeVariableLister::visit(Symbolic::ObjectBinaryOperation* obj, void* arg)
{
    obj->getLhs()->accept(this, arg);
    obj->getRhs()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::SymbolicInteger* symbolicinteger, void* arg)
{
    mResult.insert(QString(symbolicinteger->getSource().getIdentifier().c_str()), symbolicinteger->getSource().getIdentifierMethod());
}

void ExpressionFreeVariableLister::visit(Symbolic::ConstantInteger* constantinteger, void* arg)
{
}

void ExpressionFreeVariableLister::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* arg)
{
    integerbinaryoperation->getLhs()->accept(this, arg);
    integerbinaryoperation->getRhs()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::IntegerCoercion* integercoercion, void* arg)
{
    integercoercion->getExpression()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::IntegerMaxMin* obj, void* arg)
{
    std::list<Symbolic::Expression*> expressions = obj->getExpressions();
    std::list<Symbolic::Expression*>::iterator iter;

    for (iter = expressions.begin(); iter != expressions.end(); iter++) {
        Symbolic::Expression* expression = *iter;
        expression->accept(this);
    }
}

void ExpressionFreeVariableLister::visit(Symbolic::SymbolicString* symbolicstring, void* arg)
{
    mResult.insert(QString(symbolicstring->getSource().getIdentifier().c_str()), symbolicstring->getSource().getIdentifierMethod());
}

void ExpressionFreeVariableLister::visit(Symbolic::ConstantString* constantstring, void* arg)
{
}

void ExpressionFreeVariableLister::visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* arg)
{
    stringbinaryoperation->getLhs()->accept(this, arg);
    stringbinaryoperation->getRhs()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringRegexReplace* stringregexreplace, void* arg)
{
    stringregexreplace->getSource()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringRegexSubmatchArray* exp, void* arg)
{
    exp->getSource()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringRegexSubmatchArrayAt* exp, void* arg)
{
    exp->getMatch()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringRegexSubmatchArrayMatch* exp, void* arg)
{
    exp->getMatch()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringRegexSubmatch* submatch, void* arg)
{
    submatch->getSource()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringRegexSubmatchIndex* submatchIndex, void* arg)
{
    submatchIndex->getSource()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringReplace* stringreplace, void* arg)
{
    stringreplace->getSource()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringCoercion* stringcoercion, void* arg)
{
    stringcoercion->getExpression()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringCharAt* stringcharat, void* arg)
{
    stringcharat->getSource()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::SymbolicBoolean* symbolicboolean, void* arg)
{
    mResult.insert(QString(symbolicboolean->getSource().getIdentifier().c_str()), symbolicboolean->getSource().getIdentifierMethod());
}

void ExpressionFreeVariableLister::visit(Symbolic::ConstantBoolean* constantboolean, void* arg)
{
}

void ExpressionFreeVariableLister::visit(Symbolic::BooleanCoercion* booleancoercion, void* arg)
{
    booleancoercion->getExpression()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* arg)
{
    booleanbinaryoperation->getLhs()->accept(this, arg);
    booleanbinaryoperation->getRhs()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringLength* stringlength, void* arg)
{
    stringlength->getString()->accept(this, arg);
}

void ExpressionFreeVariableLister::visit(Symbolic::StringIndexOf* obj, void* arg)
{
    obj->getSource()->accept(this, arg);
    obj->getPattern()->accept(this, arg);
    obj->getOffset()->accept(this, arg);
}


} // namespace artemis
