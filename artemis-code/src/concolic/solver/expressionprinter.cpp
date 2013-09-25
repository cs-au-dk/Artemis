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

#include "expressionprinter.h"

#ifdef ARTEMIS

namespace artemis
{

ExpressionPrinter::ExpressionPrinter()
{
}

void ExpressionPrinter::visit(Symbolic::SymbolicInteger* symbolicinteger)
{
    m_result += "SymbolicInteger";
}

void ExpressionPrinter::visit(Symbolic::ConstantInteger* constantinteger)
{
    m_result += "ConstantInteger";
}

void ExpressionPrinter::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation)
{
    m_result += "(";
    integerbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(integerbinaryoperation->getOp());
    m_result += " ";
    integerbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

void ExpressionPrinter::visit(Symbolic::IntegerCoercion* integercoercion)
{
     m_result += "IntegerCoercion( ";
     integercoercion->getExpression()->accept(this);
     m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::SymbolicString* symbolicstring)
{
    m_result += "SymbolicString";
}

void ExpressionPrinter::visit(Symbolic::ConstantString* constantstring)
{
    m_result += "ConstantString";
}

void ExpressionPrinter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation)
{
    m_result += "(";
    stringbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(stringbinaryoperation->getOp());
    m_result += " ";
    stringbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

void ExpressionPrinter::visit(Symbolic::StringRegexReplace* stringregexreplace)
{
    m_result += "StringRegexReplace( ";
    stringregexreplace->getSource()->accept(this);
    m_result += ", \"";
    m_result += stringregexreplace->getRegexpattern()->data();
    m_result += "\", \"";
    m_result += stringregexreplace->getReplace()->data();
    m_result += "\" )";
}

void ExpressionPrinter::visit(Symbolic::StringReplace* stringreplace)
{
    m_result += "StringReplace( ";
    stringreplace->getSource()->accept(this);
    m_result += ", \"";
    m_result += stringreplace->getPattern()->data();
    m_result += "\", \"";
    m_result += stringreplace->getReplace()->data();
    m_result += "\" )";
}

void ExpressionPrinter::visit(Symbolic::StringCoercion* stringcoercion)
{
    m_result += "StringCoercion( ";
    stringcoercion->getExpression()->accept(this);
    m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::SymbolicBoolean* symbolicboolean)
{
    m_result += "SymbolicBoolean";
}

void ExpressionPrinter::visit(Symbolic::ConstantBoolean* constantboolean)
{
    m_result += "ConstantBoolean";
}

void ExpressionPrinter::visit(Symbolic::BooleanCoercion* booleancoercion)
{
    m_result += "BooleanCoercion( ";
    booleancoercion->getExpression()->accept(this);
    m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation)
{
    m_result += "(";
    booleanbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(booleanbinaryoperation->getOp());
    m_result += " ";
    booleanbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

void ExpressionPrinter::visit(Symbolic::StringLength* stringlength)
{
    m_result += "StringLength( ";
    stringlength->getString()->accept(this);
    m_result += " )";
}

}

#endif
