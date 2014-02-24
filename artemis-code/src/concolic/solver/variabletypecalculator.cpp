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

#include "variabletypecalculator.h"

namespace artemis
{


QMap<QString, Symbolic::Type> VariableTypeCalculator::calculateTypes(PathConditionPtr pathCondition)
{
    // For each Symbolic::Expression in the PC, call the visitor.
    // This builds the sets mStringVars, mIntVars, mBoolVars.
    for (uint i = 0; i < pathCondition->size(); i++) {
        mExpectedType = Symbolic::BOOL;
        pathCondition->get(i).first->accept(this);
    }

    // We return results in the hierarchy string > int > bool.
    // We have good coercions string->bool and int->bool so we must give those precedence over booleans.
    // Whether we have string > int or int > string is irrelevant as these will currently cause type errors in the
    // constraint writer anyway.
    // This means that we will be able to translate any constraint with no type errors as long as there is no
    // variable with both string and integer constraints on it.
    QMap<QString, Symbolic::Type> result;

    // Add the variables to the mapping, overwriting bools with ints or strings, etc.
    foreach(QString var, mBoolVars){
        result.insert(var, Symbolic::BOOL);
    }
    foreach(QString var, mIntVars){
        result.insert(var, Symbolic::INT);
    }
    foreach(QString var, mStringVars){
        result.insert(var, Symbolic::STRING);
    }

    return result;
}


/**
 * These visitors simply explore the tree keeping track of the expected type of each subexpression.
 * The expected type of each symbolic variable is recorded.
 *
 * Coercions are handled a little differently... We ignore them where possible, so that we can use a variable as it's
 * "intended type" and not always as a string. So when we see a coercion we will not change mExpectedType. Then if
 * we immediately find a variable, then that variable can be treated as the type of the resulting coercion
 * (i.e. the original value of mExpectedType ignoring the coercion). If we do not immediately see a variable,
 * then whichever subexpression we see instead can set mExpectedType as usual, because any variables in that
 * subexpression really would have to be of the pre-coerced type (the type of the subexpression arguments).
 *
 * Also there are certain subexpressions (currently StringRegexReplace and StringReplace) which are "transparent" to
 * coercions in the constraint writer. These are also made transparent here top match (i.e. the expected type is
 * simply passed on as-is).
 *
 * TODO: have some central method to determine when nodes should be transparent to coercions (possibly even
 * conditionally on their arguments, such as regex replacements only being transparent when removing whitespace) which
 * is used both here and in the constraint writer.
 *
 * For example the following expression:
 * IntegerBinaryOperation(IntegerCoercion(v1), INT_EQ, IntegerCoercion(StringBinaryOperation(v1, CONCAT, v2)))
 * Should result in the following assignment: v1: once as int and once as string, v2: once as string.
 *
 */

void VariableTypeCalculator::visit(Symbolic::SymbolicInteger *symbolicinteger, void *args)
{
    // This is a variable, so record the current expected type.
    recordCurrentType(QString::fromStdString(symbolicinteger->getSource().getIdentifier()));
}

void VariableTypeCalculator::visit(Symbolic::ConstantInteger *constantinteger, void *args)
{
    // This is a leaf, so do nothing.
}

void VariableTypeCalculator::visit(Symbolic::IntegerBinaryOperation *integerbinaryoperation, void *args)
{
    // Expecting integer subexpressions.
    mExpectedType = Symbolic::INT;
    integerbinaryoperation->getLhs()->accept(this);
    mExpectedType = Symbolic::INT;
    integerbinaryoperation->getRhs()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::IntegerCoercion *integercoercion, void *args)
{
    // Ignoring coercions (see comment above).
    mExpectedType = mExpectedType;
    integercoercion->getExpression()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::StringLength *stringlength, void *args)
{
    // Expecting a string subexpression.
    mExpectedType = Symbolic::STRING;
    stringlength->getString()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::StringRegexSubmatchIndex *submatchIndex, void *arg)
{
    // Expecting a string subexpression.
    mExpectedType = Symbolic::STRING;
    submatchIndex->getSource()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::SymbolicString *symbolicstring, void *args)
{
    // This is a variable, so record the current expected type.
    recordCurrentType(QString::fromStdString(symbolicstring->getSource().getIdentifier()));
}

void VariableTypeCalculator::visit(Symbolic::ConstantString *constantstring, void *args)
{
    // This is a leaf, so do nothing.
}

void VariableTypeCalculator::visit(Symbolic::StringBinaryOperation *stringbinaryoperation, void *args)
{
    // Expecting string subexpressions.
    mExpectedType = Symbolic::STRING;
    stringbinaryoperation->getLhs()->accept(this);
    mExpectedType = Symbolic::STRING;
    stringbinaryoperation->getRhs()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::StringCoercion *stringcoercion, void *args)
{
    // Ignoring coercions (see comment above).
    mExpectedType = mExpectedType;
    stringcoercion->getExpression()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::StringCharAt *stringcharat, void *arg)
{
    // Expecting a string subexpression.
    mExpectedType = Symbolic::STRING;
    stringcharat->getSource()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::StringRegexReplace *stringregexreplace, void *args)
{
    // Ignoring nodes which are transparent to the coercionpromise (see above).
    // This is either String->String or ignored by the constraint writer, so keeping mExpectedType as-is is sensible.
    mExpectedType = mExpectedType;
    stringregexreplace->getSource()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::StringReplace *stringreplace, void *args)
{
    // Ignoring nodes which are transparent to the coercionpromise (see above).
    // This is either String->String or ignored by the constraint writer, so keeping mExpectedType as-is is sensible.
    mExpectedType = mExpectedType;
    stringreplace->getSource()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::SymbolicBoolean *symbolicboolean, void *args)
{
    // This is a variable, so record the current expected type.
    recordCurrentType(QString::fromStdString(symbolicboolean->getSource().getIdentifier()));
}

void VariableTypeCalculator::visit(Symbolic::ConstantBoolean *constantboolean, void *args)
{
    // This is a leaf, so do nothing.
}

void VariableTypeCalculator::visit(Symbolic::BooleanCoercion *booleancoercion, void *args)
{
    // Ignoring coercions (see comment above).
    mExpectedType = mExpectedType;
    booleancoercion->getExpression()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::BooleanBinaryOperation *booleanbinaryoperation, void *args)
{
    // Expecting boolean subexpressions.
    mExpectedType = Symbolic::BOOL;
    booleanbinaryoperation->getLhs()->accept(this);
    mExpectedType = Symbolic::BOOL;
    booleanbinaryoperation->getRhs()->accept(this);
}

void VariableTypeCalculator::visit(Symbolic::StringRegexSubmatch *submatch, void *arg)
{
    // Expecting a string subexpression.
    mExpectedType = Symbolic::STRING;
    submatch->getSource()->accept(this);
}



void VariableTypeCalculator::recordCurrentType(QString var)
{
    switch(mExpectedType) {
    case Symbolic::STRING:
        mStringVars.insert(var);
        break;
    case Symbolic::BOOL:
        mBoolVars.insert(var);
        break;
    case Symbolic::INT:
        mIntVars.insert(var);
        break;
    default:
        qFatal("Error: Recording an unexpected type in VariableTypeCalculator.");
        exit(1);
    }
}


} //namespace artemis
