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
