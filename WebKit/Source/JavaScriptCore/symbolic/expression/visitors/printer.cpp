/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License") { }
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <config.h>
#include "JavaScriptCore/wtf/text/CString.h"

#include "printer.h"

#ifdef ARTEMIS

namespace Symbolic
{

Printer::Printer()
{
}

void Printer::visit(SymbolicInteger* symbolicinteger)
{
    m_result += "SymbolicInteger";
}

void Printer::visit(ConstantInteger* constantinteger)
{
    m_result += "ConstantInteger";
}

void Printer::visit(IntegerBinaryOperation* integerbinaryoperation)
{
    m_result += "(";
    integerbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(integerbinaryoperation->getOp());
    m_result += " ";
    integerbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

void Printer::visit(IntegerCoercion* integercoercion)
{
     m_result += "IntegerCoercion( ";
     integercoercion->getExpression()->accept(this);
     m_result += " )";
}

void Printer::visit(SymbolicString* symbolicstring)
{
    m_result += "SymbolicString";
}

void Printer::visit(ConstantString* constantstring)
{
    m_result += "ConstantString";
}

void Printer::visit(StringBinaryOperation* stringbinaryoperation)
{
    m_result += "(";
    stringbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(stringbinaryoperation->getOp());
    m_result += " ";
    stringbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

void Printer::visit(StringRegexReplace* stringregexreplace)
{
    m_result += "StringRegexReplace( ";
    stringregexreplace->getSource()->accept(this);
    m_result += ", \"";
    m_result += stringregexreplace->getRegexpattern()->data();
    m_result += "\", \"";
    m_result += stringregexreplace->getReplace()->data();
    m_result += "\" )";
}

void Printer::visit(StringReplace* stringreplace)
{
    m_result += "StringReplace( ";
    stringreplace->getSource()->accept(this);
    m_result += ", \"";
    m_result += stringreplace->getPattern()->data();
    m_result += "\", \"";
    m_result += stringreplace->getReplace()->data();
    m_result += "\" )";
}

void Printer::visit(StringCoercion* stringcoercion)
{
    m_result += "StringCoercion( ";
    stringcoercion->getExpression()->accept(this);
    m_result += " )";
}

void Printer::visit(SymbolicBoolean* symbolicboolean)
{
    m_result += "SymbolicBoolean";
}

void Printer::visit(ConstantBoolean* constantboolean)
{
    m_result += "ConstantBoolean";
}

void Printer::visit(BooleanCoercion* booleancoercion)
{
    m_result += "BooleanCoercion( ";
    booleancoercion->getExpression()->accept(this);
    m_result += " )";
}

void Printer::visit(BooleanBinaryOperation* booleanbinaryoperation)
{
    m_result += "(";
    booleanbinaryoperation->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(booleanbinaryoperation->getOp());
    m_result += " ";
    booleanbinaryoperation->getRhs()->accept(this);
    m_result += ")";
}

}

#endif
