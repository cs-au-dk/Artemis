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

#include <sstream>

#include "expressionprinter.h"

#ifdef ARTEMIS

namespace artemis
{

ExpressionPrinter::ExpressionPrinter()
{
}

void ExpressionPrinter::visit(Symbolic::SymbolicInteger* symbolicinteger, void* args)
{
    m_result += "SymbolicInteger";
}

void ExpressionPrinter::visit(Symbolic::ConstantInteger* constantinteger, void* args)
{
    m_result += "ConstantInteger";
}

void ExpressionPrinter::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* args)
{
    m_result += "(";
    integerbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(integerbinaryoperation->getOp());
    m_result += " ";
    integerbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

void ExpressionPrinter::visit(Symbolic::IntegerCoercion* integercoercion, void* args)
{
     m_result += "IntegerCoercion( ";
     integercoercion->getExpression()->accept(this);
     m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::SymbolicString* symbolicstring, void* args)
{
    m_result += "SymbolicString";
}

void ExpressionPrinter::visit(Symbolic::ConstantString* constantstring, void* args)
{
    m_result += "ConstantString";
}

void ExpressionPrinter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args)
{
    m_result += "(";
    stringbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(stringbinaryoperation->getOp());
    m_result += " ";
    stringbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

void ExpressionPrinter::visit(Symbolic::StringRegexReplace* stringregexreplace, void* args)
{
    m_result += "StringRegexReplace( ";
    stringregexreplace->getSource()->accept(this);
    m_result += ", \"";
    m_result += stringregexreplace->getRegexpattern()->data();
    m_result += "\", \"";
    m_result += stringregexreplace->getReplace()->data();
    m_result += "\" )";
}

void ExpressionPrinter::visit(Symbolic::StringReplace* stringreplace, void* args)
{
    m_result += "StringReplace( ";
    stringreplace->getSource()->accept(this);
    m_result += ", \"";
    m_result += stringreplace->getPattern()->data();
    m_result += "\", \"";
    m_result += stringreplace->getReplace()->data();
    m_result += "\" )";
}

void ExpressionPrinter::visit(Symbolic::StringCoercion* stringcoercion, void* args)
{
    m_result += "StringCoercion( ";
    stringcoercion->getExpression()->accept(this);
    m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::StringCharAt* stringcharat, void* arg)
{
    m_result += "StringCharAt( ";
    stringcharat->getSource()->accept(this);
    m_result += " , ";

    std::ostringstream i;
    i << stringcharat->getPosition();
    m_result += i.str();

    m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::SymbolicBoolean* symbolicboolean, void* args)
{
    m_result += "SymbolicBoolean";
}

void ExpressionPrinter::visit(Symbolic::ConstantBoolean* constantboolean, void* args)
{
    m_result += "ConstantBoolean";
}

void ExpressionPrinter::visit(Symbolic::BooleanCoercion* booleancoercion, void* args)
{
    m_result += "BooleanCoercion( ";
    booleancoercion->getExpression()->accept(this);
    m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* args)
{
    m_result += "(";
    booleanbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(booleanbinaryoperation->getOp());
    m_result += " ";
    booleanbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

void ExpressionPrinter::visit(Symbolic::StringLength* stringlength, void* args)
{
    m_result += "StringLength( ";
    stringlength->getString()->accept(this);
    m_result += " )";
}

}

#endif
