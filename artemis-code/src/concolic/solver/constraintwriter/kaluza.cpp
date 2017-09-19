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

bool KaluzaConstraintWriter::write(PathConditionPtr pathCondition, FormRestrictions formRestrictions, DomSnapshotStoragePtr domSnapshots, ReachablePathsConstraintSet reachablePaths, ReorderingConstraintInfoPtr reorderingInfo, std::string outputFile)
{
    qDebug() << "Warning: KaluzaConstraintWriter does not support implicit form restrictions, DOM snapshots, reachable paths constraints, or renaming variables.\n";

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

void KaluzaConstraintWriter::visit(Symbolic::SymbolicInteger* symbolicinteger, void* args)
{
    mIdentifierStore = symbolicinteger->getSource().getIdentifier();
}

void KaluzaConstraintWriter::visit(Symbolic::ConstantInteger* constantinteger, void* args)
{
    std::ostringstream strs;
    strs << constantinteger->getValue();

    mIdentifierStore = strs.str();
}

void KaluzaConstraintWriter::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* args)
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

void KaluzaConstraintWriter::visit(Symbolic::IntegerCoercion* integercoercion, void* args)
{
    integercoercion->getExpression()->accept(this);
}

void KaluzaConstraintWriter::visit(Symbolic::IntegerMaxMin* obj, void* arg)
{
    mError = true;
    mErrorReason = "Math max and min not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring, void* args)
{
    mIdentifierStore = symbolicstring->getSource().getIdentifier();
}

void KaluzaConstraintWriter::visit(Symbolic::ConstantString* constantstring, void* args)
{
    std::ostringstream strs;
    strs << "\"" << *constantstring->getValue() << "\"";
    mIdentifierStore = strs.str();
}

void KaluzaConstraintWriter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args)
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

void KaluzaConstraintWriter::visit(Symbolic::ConstantObject* obj, void* arg)
{
    mError = true;
    mErrorReason = "Null objects not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::ObjectBinaryOperation* obj, void* arg)
{
    mError = true;
    mErrorReason = "Null objects not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringRegexReplace*, void* args)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringRegexSubmatch* submatch, void* arg)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringRegexSubmatchIndex* submatchIndex, void* arg)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringRegexSubmatchArray* exp, void* arg)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringRegexSubmatchArrayAt* exp, void* arg)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringRegexSubmatchArrayMatch* exp, void* arg)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringReplace*, void* args)
{
    mError = true;
    mErrorReason = "String replace constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion, void* args)
{
    stringcoercion->getExpression()->accept(this);
}

void KaluzaConstraintWriter::visit(Symbolic::StringCharAt* stringcharat, void* arg)
{
    mError = true;
    mErrorReason = "StringCharAt constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::SymbolicBoolean* symbolicboolean, void* args)
{
    mIdentifierStore = symbolicboolean->getSource().getIdentifier();
}

void KaluzaConstraintWriter::visit(Symbolic::ConstantBoolean* constantboolean, void* args)
{
    mIdentifierStore = constantboolean->getValue() == true ? "true" : "false";
}

void KaluzaConstraintWriter::visit(Symbolic::BooleanCoercion* booleancoercion, void* args)
{
    booleancoercion->getExpression()->accept(this);
}

void KaluzaConstraintWriter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* args)
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

void KaluzaConstraintWriter::visit(Symbolic::StringLength* stringlength, void* args)
{
    mError = true;
    mErrorReason = "String length constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringIndexOf* obj, void* args)
{
    mError = true;
    mErrorReason = "String index of constraints not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::SymbolicObject* obj, void* arg)
{
    mError = true;
    mErrorReason = "Symbolic objects not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::ObjectArrayIndexOf* obj, void* arg)
{
    mError = true;
    mErrorReason = "Array index for objects not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::SymbolicObjectPropertyString* obj, void* arg)
{
    mError = true;
    mErrorReason = "Symbolic node properties not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringSubstring* obj, void* arg)
{
    mError = true;
    mErrorReason = "Symbolic string substring not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringToLowerCase *stringtolowercase, void *arg)
{
    mError = true;
    mErrorReason = "Symbolic string toLowerCase not supported";
    mIdentifierStore = "ERROR";
}

void KaluzaConstraintWriter::visit(Symbolic::StringToUpperCase *stringtouppercase, void *arg)
{
    mError = true;
    mErrorReason = "Symbolic string toUpperCase not supported";
    mIdentifierStore = "ERROR";
}

}

#endif
