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

#ifndef EXPRESSIONFREEVARIABLELISTER_H
#define EXPRESSIONFREEVARIABLELISTER_H

#include <QMap>
#include <QString>

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"
#include "JavaScriptCore/symbolic/expression/symbolicsource.h"

namespace artemis
{

class ExpressionFreeVariableLister: public Symbolic::Visitor
{
public:

    void visit(Symbolic::SymbolicInteger* symbolicinteger, void* arg);
    void visit(Symbolic::ConstantInteger* constantinteger, void* arg);
    void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* arg);
    void visit(Symbolic::IntegerCoercion* integercoercion, void* arg);
    void visit(Symbolic::SymbolicString* symbolicstring, void* arg);
    void visit(Symbolic::ConstantString* constantstring, void* arg);
    void visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* arg);
    void visit(Symbolic::StringCoercion* stringcoercion, void* arg);
    void visit(Symbolic::StringCharAt* stringcharat, void* arg);
    void visit(Symbolic::StringRegexReplace* stringregexreplace, void* arg);
    void visit(Symbolic::StringRegexSubmatch* submatch, void* arg);
    void visit(Symbolic::StringRegexSubmatchIndex* submatchIndex, void* arg);
    void visit(Symbolic::StringReplace* stringreplace, void* arg);
    void visit(Symbolic::SymbolicBoolean* symbolicboolean, void* arg);
    void visit(Symbolic::ConstantBoolean* constantboolean, void* arg);
    void visit(Symbolic::BooleanCoercion* booleancoercion, void* arg);
    void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* arg);
    void visit(Symbolic::StringLength* stringlength, void* arg);

    inline QMap<QString, Symbolic::SourceIdentifierMethod> getResult() const {
        return mResult;
    }

    inline void clear() {
        mResult.clear();
    }

protected:
    // The reason we do not have a SymbolicSource itself as a result is because it cannot be placed into Qt collections.
    QMap<QString, Symbolic::SourceIdentifierMethod> mResult;
};


} //namespace artemis

#endif // EXPRESSIONFREEVARIABLELISTER_H
