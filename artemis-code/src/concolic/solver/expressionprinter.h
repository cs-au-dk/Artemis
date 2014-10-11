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

#ifndef PRINTER_H
#define PRINTER_H

#include <string>

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"


namespace artemis
{

class ExpressionPrinter : public Symbolic::Visitor
{

public:
    ExpressionPrinter();
    virtual ~ExpressionPrinter(){}

    void visit(Symbolic::ConstantObject* obj, void* arg);
    void visit(Symbolic::ObjectBinaryOperation* obj, void* arg);
    void visit(Symbolic::SymbolicInteger* symbolicinteger, void* arg);
    void visit(Symbolic::ConstantInteger* constantinteger, void* arg);
    void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* arg);
    void visit(Symbolic::IntegerCoercion* integercoercion, void* arg);
    void visit(Symbolic::IntegerMaxMin* obj, void* arg);
    void visit(Symbolic::SymbolicString* symbolicstring, void* arg);
    void visit(Symbolic::ConstantString* constantstring, void* arg);
    void visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* arg);
    void visit(Symbolic::StringCoercion* stringcoercion, void* arg);
    void visit(Symbolic::StringCharAt* stringcharat, void* arg);
    void visit(Symbolic::StringRegexReplace* stringregexreplace, void* arg);
    void visit(Symbolic::StringReplace* stringreplace, void* arg);
    void visit(Symbolic::StringRegexSubmatch* submatch, void* arg);
    void visit(Symbolic::StringRegexSubmatchIndex* submatchIndex, void* arg);
    void visit(Symbolic::StringRegexSubmatchArray* exp, void* arg);
    void visit(Symbolic::StringRegexSubmatchArrayAt* exp, void* arg);
    void visit(Symbolic::StringRegexSubmatchArrayMatch* exp, void* arg);
    void visit(Symbolic::SymbolicBoolean* symbolicboolean, void* arg);
    void visit(Symbolic::ConstantBoolean* constantboolean, void* arg);
    void visit(Symbolic::BooleanCoercion* booleancoercion, void* arg);
    void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* arg);
    void visit(Symbolic::StringLength* stringlength, void* arg);
    void visit(Symbolic::StringIndexOf* stringindexof, void* arg);
    void visit(Symbolic::SymbolicObject* symbolicobject, void* arg);
    void visit(Symbolic::ObjectArrayIndexOf* objectarrayindexof, void* arg);
    void visit(Symbolic::SymbolicObjectPropertyString* obj, void* arg);

    inline std::string getResult() const {
        return m_result;
    }

    void clear() {
        m_result.clear();
    }

protected:
    std::string m_result;

};

}

#endif // PRINTER_H
