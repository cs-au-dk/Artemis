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

#include <cstdlib>
#include <iostream>
#include <ostream>
#include <sstream>

#include "constraintwriter.h"

#ifdef ARTEMIS

namespace artemis
{

ConstraintWriter::ConstraintWriter(std::string output_filename) :
    mNextTemporaryIdentifier(0),
    mError(false)
{
    mOutput.open(output_filename.data());
}

bool ConstraintWriter::commit()
{
    mOutput.close();

    if (mError) {
        std::cerr << "Artemis is unable generate constraints - " << mErrorReason << "." << std::endl;
        return false;
    }

    for (std::map<std::string, Type>::iterator iter = mTypemap.begin(); iter != mTypemap.end(); iter++) {
        if (iter->second == TYPEERROR) {
            std::cerr << "Artemis is unable generate constraints - a type-error was found." << std::endl;
            return false;
        }
    }

    return true;
}

void ConstraintWriter::visit(Symbolic::SymbolicInteger* symbolicinteger)
{
    mIdentifierStore = *symbolicinteger->getIdentifier();
}

void ConstraintWriter::visit(Symbolic::ConstantInteger* constantinteger)
{
    std::ostringstream strs;
    strs << constantinteger->getValue();

    mIdentifierStore = strs.str();
}

void ConstraintWriter::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation)
{
    integerbinaryoperation->getLhs()->accept(this);
    std::string lhs = mIdentifierStore;
    recordType(lhs, INT);

    integerbinaryoperation->getRhs()->accept(this);
    std::string rhs = mIdentifierStore;
    recordType(rhs, INT);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = strs.str();
    recordType(mIdentifierStore, INT);

    mOutput << mIdentifierStore << " := " << lhs << " " << opToString(integerbinaryoperation->getOp()) << " " << rhs << ";\n";
}

void ConstraintWriter::visit(Symbolic::IntegerCoercion* integercoercion)
{
    integercoercion->getExpression()->accept(this);
}

void ConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring)
{
    mIdentifierStore = *symbolicstring->getIdentifier();
}

void ConstraintWriter::visit(Symbolic::ConstantString* constantstring)
{
    std::ostringstream strs;
    strs << "\"" << *constantstring->getValue() << "\"";
    mIdentifierStore = strs.str();
}

void ConstraintWriter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation)
{
    stringbinaryoperation->getLhs()->accept(this);
    std::string lhs = mIdentifierStore;
    recordType(lhs, STRING);

    stringbinaryoperation->getRhs()->accept(this);
    std::string rhs = mIdentifierStore;
    recordType(rhs, STRING);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = strs.str();
    recordType(mIdentifierStore, STRING);

    mOutput << mIdentifierStore << " := " << lhs << " " << opToString(stringbinaryoperation->getOp()) << " " << rhs << ";\n";
}

void ConstraintWriter::visit(Symbolic::StringRegexReplace*)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mIdentifierStore = "ERROR";
}

void ConstraintWriter::visit(Symbolic::StringReplace*)
{
    mError = true;
    mErrorReason = "String replace constraints not supported";
    mIdentifierStore = "ERROR";
}

void ConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion)
{
    stringcoercion->getExpression()->accept(this);
}

void ConstraintWriter::visit(Symbolic::SymbolicBoolean* symbolicboolean)
{
    mIdentifierStore = *symbolicboolean->getIdentifier();
}

void ConstraintWriter::visit(Symbolic::ConstantBoolean* constantboolean)
{
    mIdentifierStore = constantboolean->getValue() == true ? "true" : "false";
}

void ConstraintWriter::visit(Symbolic::BooleanCoercion* booleancoercion)
{
    booleancoercion->getExpression()->accept(this);
}

void ConstraintWriter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation)
{
    booleanbinaryoperation->getLhs()->accept(this);
    std::string lhs = mIdentifierStore;
    recordType(lhs, BOOL);

    booleanbinaryoperation->getRhs()->accept(this);
    std::string rhs = mIdentifierStore;
    recordType(rhs, BOOL);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = strs.str();
    recordType(mIdentifierStore, BOOL);

    mOutput << mIdentifierStore << " := " << lhs << " " << opToString(booleanbinaryoperation->getOp()) << " " << rhs << ";\n";
}

void ConstraintWriter::recordType(const std::string& identifier, Type type)
{

    std::map<std::string, Type>::iterator iter = mTypemap.find(identifier);

    if (iter != mTypemap.end()) {
        iter->second = iter->second == type ? type : TYPEERROR;
    } else {
        mTypemap.insert(std::pair<std::string, Type>(identifier, type));
    }

}


}

#endif
