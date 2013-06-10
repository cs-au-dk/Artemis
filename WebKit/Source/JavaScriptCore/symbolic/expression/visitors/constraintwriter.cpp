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

#include <iostream>
#include <ostream>
#include <sstream>

#include <config.h>
#include "JavaScriptCore/wtf/text/CString.h"

#include "constraintwriter.h"

#ifdef ARTEMIS

namespace Symbolic
{

ConstraintWriter::ConstraintWriter(std::string output_filename) :
    mNextTemporaryIdentifier(0)
{
    mOutput.open(output_filename.data());
}

bool ConstraintWriter::commit()
{
    bool typeError = false;

    for (std::map<std::string, Type>::iterator iter = mTypemap.begin(); iter != mTypemap.end(); iter++) {
        typeError = typeError || iter->second;
    }

    if (typeError) {
        std::cerr << "Artemis is unable generate constraints - a type-error was found." << std::endl;
    }

    mOutput.close();

    return !typeError;
}

void ConstraintWriter::visit(SymbolicInteger* symbolicinteger)
{
    mIdentifierStore = symbolicinteger->getIdentifier();
}

void ConstraintWriter::visit(ConstantInteger* constantinteger)
{
    std::ostringstream strs;
    strs << constantinteger->getValue();

    mIdentifierStore = new std::string(strs.str());
}

void ConstraintWriter::visit(IntegerBinaryOperation* integerbinaryoperation)
{
    integerbinaryoperation->getLhs()->accept(this);
    std::string* lhs = mIdentifierStore;
    recordType(*lhs, INT);

    integerbinaryoperation->getRhs()->accept(this);
    std::string* rhs = mIdentifierStore;
    recordType(*rhs, INT);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = new std::string(strs.str());
    recordType(*mIdentifierStore, INT);

    mOutput << *mIdentifierStore << " := " << *lhs << " " << opToString(integerbinaryoperation->getOp()) << " " << *rhs << ";\n";
}

void ConstraintWriter::visit(IntegerCoercion* integercoercion)
{
    integercoercion->getExpression()->accept(this);
}

void ConstraintWriter::visit(SymbolicString* symbolicstring)
{
    mIdentifierStore = symbolicstring->getIdentifier();
}

void ConstraintWriter::visit(ConstantString* constantstring)
{
    std::ostringstream strs;
    strs << "\"" << *constantstring->getValue() << "\"";
    mIdentifierStore = new std::string(strs.str());
}

void ConstraintWriter::visit(StringBinaryOperation* stringbinaryoperation)
{
    stringbinaryoperation->getLhs()->accept(this);
    std::string* lhs = mIdentifierStore;
    recordType(*lhs, STRING);

    stringbinaryoperation->getRhs()->accept(this);
    std::string* rhs = mIdentifierStore;
    recordType(*rhs, STRING);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = new std::string(strs.str());
    recordType(*mIdentifierStore, STRING);

    mOutput << *mIdentifierStore << " := " << *lhs << " " << opToString(stringbinaryoperation->getOp()) << " " << *rhs << ";\n";
}

void ConstraintWriter::visit(StringRegexReplace* stringregexreplace)
{
    std::cerr << "Regex constraints not supported" << std::endl;
    std::exit(1);
}

void ConstraintWriter::visit(StringReplace* stringreplace)
{
    std::cerr << "String replace constraints not supported" << std::endl;
    std::exit(1);
}

void ConstraintWriter::visit(StringCoercion* stringcoercion)
{
    stringcoercion->getExpression()->accept(this);
}

void ConstraintWriter::visit(SymbolicBoolean* symbolicboolean)
{
    mIdentifierStore = symbolicboolean->getIdentifier();
}

void ConstraintWriter::visit(ConstantBoolean* constantboolean)
{
    mIdentifierStore = new std::string(constantboolean->getValue() == true ? "true" : "false");
}

void ConstraintWriter::visit(BooleanCoercion* booleancoercion)
{
    booleancoercion->getExpression()->accept(this);
}

void ConstraintWriter::visit(BooleanBinaryOperation* booleanbinaryoperation)
{
    booleanbinaryoperation->getLhs()->accept(this);
    std::string* lhs = mIdentifierStore;
    recordType(*lhs, BOOL);

    booleanbinaryoperation->getRhs()->accept(this);
    std::string* rhs = mIdentifierStore;
    recordType(*rhs, BOOL);

    // construct temporary identifier
    std::ostringstream strs;
    strs << "tmp";
    strs << mNextTemporaryIdentifier++;

    mIdentifierStore = new std::string(strs.str());
    recordType(*mIdentifierStore, BOOL);

    mOutput << *mIdentifierStore << " := " << *lhs << " " << opToString(booleanbinaryoperation->getOp()) << " " << *rhs << ";\n";
}

void ConstraintWriter::recordType(const std::string& identifier, Type type)
{

    std::map<std::string, Type>::iterator iter = mTypemap.find(identifier);

    if (iter != mTypemap.end()) {
        iter->second = iter->second == type ? type : ERROR;
    } else {
        mTypemap.insert(std::pair<std::string, Type>(identifier, type));
    }

}


}

#endif
