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

#ifndef VARIABLETYPECALCULATOR_H
#define VARIABLETYPECALCULATOR_H

#include <QString>
#include <QSet>
#include <QMap>

#include "concolic/pathcondition.h"
#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"

namespace artemis
{

/**
 * Calculates the types which should be assigned to each variable in a PC.
 * There is no error or type checking done as it is expected that this will be done
 * by the constraint writer itself.
 * See the calculateTypes method for a description of how any conflicts are resolved.
 * See the comment in variabletypecalculator.cpp fopr how coercions are handled.
 */
class VariableTypeCalculator : public Symbolic::Visitor
{
    friend class VariableTypeCalculatorTest;

public:
    QMap<QString, Symbolic::Type> calculateTypes(PathConditionPtr pathCondition);

protected:
    // Results in integer expressions
    virtual void visit(Symbolic::SymbolicInteger* symbolicinteger, void* args);
    virtual void visit(Symbolic::ConstantInteger* constantinteger, void* args);
    virtual void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* args);
    virtual void visit(Symbolic::IntegerCoercion* integercoercion, void* args);
    virtual void visit(Symbolic::StringLength* stringlength, void* args);
    virtual void visit(Symbolic::StringRegexSubmatchIndex* submatchIndex, void* arg);

    // Results in string expressions
    virtual void visit(Symbolic::SymbolicString* symbolicstring, void* args);
    virtual void visit(Symbolic::ConstantString* constantstring, void* args);
    virtual void visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args);
    virtual void visit(Symbolic::StringCoercion* stringcoercion, void* args);
    virtual void visit(Symbolic::StringCharAt* stringcharat, void* arg);
    virtual void visit(Symbolic::StringRegexReplace* stringregexreplace, void* args);
    virtual void visit(Symbolic::StringReplace* stringreplace, void* args);

    // Results in boolean expressions
    virtual void visit(Symbolic::SymbolicBoolean* symbolicboolean, void* args);
    virtual void visit(Symbolic::ConstantBoolean* constantboolean, void* args);
    virtual void visit(Symbolic::BooleanCoercion* booleancoercion, void* args);
    virtual void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* args);
    virtual void visit(Symbolic::StringRegexSubmatch* submatch, void* arg);

private:
    // Log of the types each variables was used as in the PC.
    // These sets are filled in by the visitors to each Symbolic::Expression.
    // It is up to calculateTypes() to determine how to manage any conflicts.
    QSet<QString> mStringVars;
    QSet<QString> mIntVars;
    QSet<QString> mBoolVars;

    // The expected type of the expression visit() is being called on.
    Symbolic::Type mExpectedType;

    // Record a variable name with the current expected type.
    void recordCurrentType(QString var);
};

} // namespace artemis
#endif // VARIABLETYPECALCULATOR_H
