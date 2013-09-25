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

    void visit(Symbolic::SymbolicInteger* symbolicinteger);
    void visit(Symbolic::ConstantInteger* constantinteger);
    void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation);
    void visit(Symbolic::IntegerCoercion* integercoercion);
    void visit(Symbolic::SymbolicString* symbolicstring);
    void visit(Symbolic::ConstantString* constantstring);
    void visit(Symbolic::StringBinaryOperation* stringbinaryoperation);
    void visit(Symbolic::StringCoercion* stringcoercion);
    void visit(Symbolic::StringRegexReplace* stringregexreplace);
    void visit(Symbolic::StringReplace* stringreplace);
    void visit(Symbolic::SymbolicBoolean* symbolicboolean);
    void visit(Symbolic::ConstantBoolean* constantboolean);
    void visit(Symbolic::BooleanCoercion* booleancoercion);
    void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation);
    void visit(Symbolic::StringLength* stringlength);

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
