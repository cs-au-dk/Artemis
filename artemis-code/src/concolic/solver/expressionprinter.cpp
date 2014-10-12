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

void ExpressionPrinter::visit(Symbolic::ConstantObject* obj, void* arg)
{
    m_result += "ConstantObject";
}

void ExpressionPrinter::visit(Symbolic::ObjectBinaryOperation* obj, void* arg)
{
    m_result += "(";
    obj->getLhs()->accept(this);
    m_result += " ";
    m_result += opToString(obj->getOp());
    m_result += " ";
    obj->getRhs()->accept(this);
    m_result += ")";
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

void ExpressionPrinter::visit(Symbolic::IntegerMaxMin* obj, void* arg)
{
    if (obj->getMax()) {
        m_result += "IntegerMax( ";
    } else {
        m_result += "IntegerMin( ";
    }

    std::list<Symbolic::Expression*> expressions = obj->getExpressions();
    std::list<Symbolic::Expression*>::iterator iter;

    for (iter = expressions.begin(); iter != expressions.end(); iter++) {
        if (iter != expressions.begin()) {
            m_result += ", ";
        }

        Symbolic::Expression* expression = *iter;
        expression->accept(this);
    }

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

void ExpressionPrinter::visit(Symbolic::StringReplace* stringreplace, void* arg)
{
    m_result += "StringReplace( ";
    stringreplace->getSource()->accept(this);
    m_result += ", \"";
    m_result += stringreplace->getPattern()->data();
    m_result += "\", \"";
    m_result += stringreplace->getReplace()->data();
    m_result += "\" )";
}

void ExpressionPrinter::visit(Symbolic::StringRegexSubmatch* submatch, void* arg)
{
    m_result += "StringRegexSubmatch( ";
    submatch->getSource()->accept(this);
    m_result += ", \"";
    m_result += submatch->getRegexpattern()->data();
    m_result += "\" )";
}

void ExpressionPrinter::visit(Symbolic::StringRegexSubmatchIndex* submatchIndex, void* arg)
{
    m_result += "StringRegexSubmatchIndex( ";
    submatchIndex->getSource()->accept(this);
    m_result += ", \"";
    m_result += submatchIndex->getRegexpattern()->data();
    m_result += "\" )";
}

void ExpressionPrinter::visit(Symbolic::StringRegexSubmatchArray* exp, void* arg)
{
    m_result += "StringRegexSubmatchArray( ";
    exp->getSource()->accept(this);
    m_result += ", \"";
    m_result += exp->getRegexpattern()->data();
    m_result += "\" )";
}

void ExpressionPrinter::visit(Symbolic::StringRegexSubmatchArrayAt* exp, void* arg)
{
    std::stringstream s;
    s << exp->getGroup();

    m_result += "StringRegexSubmatchArrayAt( ";
    exp->getMatch()->accept(this);
    m_result += ", ";
    m_result += s.str();
    m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::StringRegexSubmatchArrayMatch* exp, void* arg)
{
    m_result += "StringRegexSubmatchArrayMatch( ";
    exp->getMatch()->accept(this);
    m_result += ")";
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

void ExpressionPrinter::visit(Symbolic::StringIndexOf* obj, void* args)
{
    m_result += "StringIndexOf( ";
    obj->getSource()->accept(this);
    m_result += " , ";
    obj->getPattern()->accept(this);
    m_result += " , ";
    obj->getOffset()->accept(this);
    m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::SymbolicObject* obj, void* arg)
{
    m_result += "SymbolicObject( ";
    m_result += obj->getSource().getIdentifier();
    m_result += " )";
}

void ExpressionPrinter::visit(Symbolic::ObjectArrayIndexOf* obj, void* arg)
{
    m_result += "ObjectArrayIndexOf( ";
    obj->getSearchelement()->accept(this);
    m_result += " , [";

    std::list<Symbolic::Expression*> list = obj->getArray();
    std::list<Symbolic::Expression*>::iterator it = list.begin();
    for (; it != list.end(); ++it) {
        Symbolic::Expression* elm = (*it);
        elm->accept(this);
        m_result += " , ";
    }

    m_result += " ])";

}

void ExpressionPrinter::visit(Symbolic::SymbolicObjectPropertyString* obj, void* arg)
{
    m_result += "SymbolicProperty( ";
    obj->getObj()->accept(this);
    m_result += " )";
}

}

#endif
