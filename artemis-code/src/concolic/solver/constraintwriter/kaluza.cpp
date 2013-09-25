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

#include <cstdlib>
#include <iostream>
#include <ostream>
#include <sstream>

#include <QDebug>

#include "util/loggingutil.h"

#include "kaluza.h"

#ifdef ARTEMIS

namespace artemis
{

KaluzaConstraintWriter::KaluzaConstraintWriter() :
    mNextTemporaryIdentifier(0),
    mError(false)
{

}

bool KaluzaConstraintWriter::write(PathConditionPtr pathCondition, std::string outputFile)
{
    mNextTemporaryIdentifier = 0;
    mError = false;

    mOutput.open(outputFile.data());

    for (uint i = 0; i < pathCondition->size(); i++) {
        pathCondition->get(i);
        pathCondition->get(i).first;
        pathCondition->get(i).first->accept(this);

        if (pathCondition->get(i).second) {
            mOutput << mIdentifierStore << " == true;\n\n";
        } else {
            mOutput << mIdentifierStore << " == false;\n\n";
        }

    }

    mOutput.close();

    if (mError) {
        Log::warning("Artemis is unable generate constraints - " + mErrorReason + ".");
        return false;
    }

    for (std::map<std::string, Symbolic::Type>::iterator iter = mTypemap.begin(); iter != mTypemap.end(); iter++) {
        if (iter->second == Symbolic::TYPEERROR) {
            Log::warning("Artemis is unable generate constraints - a type-error was found.");
            return false;
        }
    }

    return true;
}

void KaluzaConstraintWriter::visit(Symbolic::SymbolicInteger* symbolicinteger)
{
    mIdentifierStore = symbolicinteger->getSource().getIdentifier();
}

void KaluzaConstraintWriter::visit(Symbolic::ConstantInteger* constantinteger)
{
    std::ostringstream strs;
    strs << constantinteger->getValue();

    mIdentifierStore = strs.str();
}

void KaluzaConstraintWriter::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation)
{
    integerbinaryoperation->getLhs()->accept(this);
    std::string lhs = mIdentifierStore;
    recordType(lhs, Symbolic::INT);

    integerbinaryoperation->getRhs()->accept(this);
    std::string rhs = mIdentifierStore;
    recordType(rhs, Symbolic::INT);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = strs.str();
    recordType(mIdentifierStore, Symbolic::opGetType(integerbinaryoperation->getOp()));

    mOutput << mIdentifierStore << " := " << lhs << " " << opToString(integerbinaryoperation->getOp()) << " " << rhs << ";\n";
}

void KaluzaConstraintWriter::visit(Symbolic::IntegerCoercion* integercoercion)
{
    integercoercion->getExpression()->accept(this);
}

void KaluzaConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring)
{
    mIdentifierStore = symbolicstring->getSource().getIdentifier();
}

void KaluzaConstraintWriter::visit(Symbolic::ConstantString* constantstring)
{
    std::ostringstream strs;
    strs << "\"" << *constantstring->getValue() << "\"";
    mIdentifierStore = strs.str();
}

void KaluzaConstraintWriter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation)
{
    stringbinaryoperation->getLhs()->accept(this);
    std::string lhs = mIdentifierStore;
    recordType(lhs, Symbolic::STRING);

    stringbinaryoperation->getRhs()->accept(this);
    std::string rhs = mIdentifierStore;
    recordType(rhs, Symbolic::STRING);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = strs.str();
    recordType(mIdentifierStore, Symbolic::opGetType(stringbinaryoperation->getOp()));

    mOutput << mIdentifierStore << " := " << lhs << " " << opToString(stringbinaryoperation->getOp()) << " " << rhs << ";\n";
}

void KaluzaConstraintWriter::visit(Symbolic::StringRegexReplace*)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringReplace*)
{
    mError = true;
    mErrorReason = "String replace constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion)
{
    stringcoercion->getExpression()->accept(this);
}

void KaluzaConstraintWriter::visit(Symbolic::SymbolicBoolean* symbolicboolean)
{
    mIdentifierStore = symbolicboolean->getSource().getIdentifier();
}

void KaluzaConstraintWriter::visit(Symbolic::ConstantBoolean* constantboolean)
{
    mIdentifierStore = constantboolean->getValue() == true ? "true" : "false";
}

void KaluzaConstraintWriter::visit(Symbolic::BooleanCoercion* booleancoercion)
{
    booleancoercion->getExpression()->accept(this);
}

void KaluzaConstraintWriter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation)
{
    booleanbinaryoperation->getLhs()->accept(this);
    std::string lhs = mIdentifierStore;
    recordType(lhs, Symbolic::BOOL);

    booleanbinaryoperation->getRhs()->accept(this);
    std::string rhs = mIdentifierStore;
    recordType(rhs, Symbolic::BOOL);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = strs.str();
    recordType(mIdentifierStore, Symbolic::opGetType(booleanbinaryoperation->getOp()));

    mOutput << mIdentifierStore << " := " << lhs << " " << opToString(booleanbinaryoperation->getOp()) << " " << rhs << ";\n";
}

void KaluzaConstraintWriter::recordType(const std::string& identifier, Symbolic::Type type)
{

    std::map<std::string, Symbolic::Type>::iterator iter = mTypemap.find(identifier);

    if (iter != mTypemap.end()) {
        iter->second = iter->second == type ? type : Symbolic::TYPEERROR;
    } else {
        mTypemap.insert(std::pair<std::string, Symbolic::Type>(identifier, type));
    }

}

void KaluzaConstraintWriter::visit(Symbolic::StringLength* stringlength)
{
    mError = true;
    mErrorReason = "String length constraints not supported";
    mIdentifierStore = "ERROR";
}


}

#endif
