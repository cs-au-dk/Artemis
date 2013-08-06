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

#include <assert.h>
#include <cstdlib>
#include <iostream>
#include <ostream>
#include <sstream>
#include <cstdlib>

#include <QDebug>

#include "z3str.h"

namespace artemis
{

Z3STRConstraintWriter::Z3STRConstraintWriter() :
    mExpressionType(Symbolic::TYPEERROR),
    mError(false)
{
}

bool Z3STRConstraintWriter::write(PathConditionPtr pathCondition, std::string outputFile)
{
    mError = false;

    mOutput.open(outputFile.data());

    for (uint i = 0; i < pathCondition->size(); i++) {

        mExpressionType = Symbolic::BOOL;
        pathCondition->get(i).first->accept(this);

        mOutput << "(assert (= " << mExpressionBuffer;
        mOutput << (pathCondition->get(i).second ? " true" : " false");
        mOutput << "))\n";

    }

    mOutput.close();

    if (mError) {
        std::string error = std::string("Artemis is unable generate constraints - ") + mErrorReason + ".";
        qDebug(error.c_str());
        return false;
    }

    for (std::map<std::string, Symbolic::Type>::iterator iter = mTypemap.begin(); iter != mTypemap.end(); iter++) {
        if (iter->second == Symbolic::TYPEERROR) {
            qDebug("Artemis is unable generate constraints - a type-error was found.");
            return false;
        }
    }

    return true;
}

void Z3STRConstraintWriter::visit(Symbolic::SymbolicInteger* symbolicinteger)
{
    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicinteger->getSource().getIdentifier());
    recordAndEmitType(symbolicinteger->getSource(), mExpressionType);
}

void Z3STRConstraintWriter::visit(Symbolic::ConstantInteger* constantinteger)
{
    std::ostringstream strs;

    switch (mExpressionType) {
    case Symbolic::INT:
        strs << constantinteger->getValue();
        break;
    case Symbolic::STRING:
        strs << "\"" << constantinteger->getValue() << "\"";
        break;
    case Symbolic::BOOL:
        strs << (constantinteger->getValue() == 0 ? "false" : "true");
        break;
    default:
        mError = true;
        mErrorReason = "Unsupported type coercion from integer to UNKNOWN";
        break;
    }

    mExpressionBuffer = strs.str();
}

void Z3STRConstraintWriter::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation)
{
    static const char* op[] = {
        "+", "-", "*", "/", "=", "!=", "<=", "<", ">=", ">", "%", "!=", "="
    };

    mExpressionType = Symbolic::INT;
    integerbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;

    mExpressionType = Symbolic::INT;
    integerbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;

    std::ostringstream strs;
    strs << "(" << op[integerbinaryoperation->getOp()] << " " << lhs << " " << rhs << ")";

    // coercion

    switch (mExpressionType) {
    case Symbolic::INT:
        mExpressionBuffer = strs.str();
        break; // no coercion

    case Symbolic::BOOL:
        mExpressionBuffer = "(> " + strs.str() + " 0)";
        break;

    case Symbolic::STRING:
        mError = true;
        mErrorReason = "Unsupported type coercion from integer to string";
        break;

    default:
        mError = true;
        mErrorReason = "Unsupported type coercion from integer to UNKNOWN";
        break;
    }
}

void Z3STRConstraintWriter::visit(Symbolic::IntegerCoercion* integercoercion)
{
    integercoercion->getExpression()->accept(this);
    assert(checkType(Symbolic::INT));
}

void Z3STRConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring)
{
    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicstring->getSource().getIdentifier());
    recordAndEmitType(symbolicstring->getSource(), mExpressionType);
}

void Z3STRConstraintWriter::visit(Symbolic::ConstantString* constantstring)
{
    std::ostringstream strs;

    switch (mExpressionType) {
    case Symbolic::INT:
        strs << atoi(constantstring->getValue()->c_str());
        break;
    case Symbolic::STRING:
        strs << "\"" << *constantstring->getValue() << "\"";
        break;
    case Symbolic::BOOL:
        strs << (constantstring->getValue()->compare("true") == 0 ? "true" : "false");
        break;
    default:
        mError = true;
        mErrorReason = "Unsupported type coercion from string to UNKNOWN";
        break;
    }

    mExpressionBuffer = strs.str();
}

void Z3STRConstraintWriter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation)
{
    static const char* op[] = {
        "+", "=", "!=", "<", "<=", ">", ">=", "=", "!="
    };

    mExpressionType = Symbolic::STRING;
    stringbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;

    mExpressionType = Symbolic::STRING;
    stringbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;

    std::ostringstream strs;
    strs << "(" << op[stringbinaryoperation->getOp()] << " " << lhs << " " << rhs << ")";

    // coercion

    switch (mExpressionType) {
    case Symbolic::INT:
        mError = true;
        mErrorReason = "Unsupported type coercion from string to integer";
        break; // no coercion

    case Symbolic::BOOL:
        mExpressionBuffer = "(= " + strs.str() + " \"true\")";
        break;

    case Symbolic::STRING:
        mExpressionBuffer = strs.str();
        break;

    default:
        mError = true;
        mErrorReason = "Unsupported type coercion from string to UNKNOWN";
        break;
    }
}

void Z3STRConstraintWriter::visit(Symbolic::StringRegexReplace*)
{
    mError = true;
    mErrorReason = "Regex constraints not supported";
    mExpressionBuffer = "ERROR";
}

void Z3STRConstraintWriter::visit(Symbolic::StringReplace*)
{
    mError = true;
    mErrorReason = "String replace constraints not supported";
    mExpressionBuffer = "ERROR";
}

void Z3STRConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion)
{
    stringcoercion->getExpression()->accept(this);
}

void Z3STRConstraintWriter::visit(Symbolic::SymbolicBoolean* symbolicboolean)
{
    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicboolean->getSource().getIdentifier());
    recordAndEmitType(symbolicboolean->getSource(), mExpressionType);
}

void Z3STRConstraintWriter::visit(Symbolic::ConstantBoolean* constantboolean)
{
    std::ostringstream strs;

    switch (mExpressionType) {
    case Symbolic::INT:
        strs << (constantboolean->getValue() == true ? "1" : "0");
        break;
    case Symbolic::STRING:
        strs << "\"" << (constantboolean->getValue() == true ? "true" : "false") << "\"";
        break;
    case Symbolic::BOOL:
        strs << (constantboolean->getValue() == true ? "true" : "false");
        break;
    default:
        mError = true;
        mErrorReason = "Unsupported type coersion from bool to UNKNOWN";
        break;
    }

    mExpressionBuffer = strs.str();
}

void Z3STRConstraintWriter::visit(Symbolic::BooleanCoercion* booleancoercion)
{
    booleancoercion->getExpression()->accept(this);
}

void Z3STRConstraintWriter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation)
{
    static const char* op[] = {
        "=", "!=", "=", "!="
    };

    mExpressionType = Symbolic::BOOL;
    booleanbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;

    mExpressionType = Symbolic::BOOL;
    booleanbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;

    std::ostringstream strs;
    strs << "(" << op[booleanbinaryoperation->getOp()] << " " << lhs << " " << rhs << ")";

    // coercion

    switch (mExpressionType) {
    case Symbolic::INT:
        mError = true;
        mErrorReason = "Unsupported type coercion from bool to integer";
        break;

    case Symbolic::BOOL:
        mExpressionBuffer = strs.str();
        break;

    case Symbolic::STRING:
        mError = true;
        mErrorReason = "Unsupported type coercion from bool to string";
        break;

    default:
        mError = true;
        mErrorReason = "Unsupported type coercion from bool to UNKNOWN";
        break;
    }
}

void Z3STRConstraintWriter::recordAndEmitType(const Symbolic::SymbolicSource& source, Symbolic::Type type)
{
    static const char* typeStrings[] = {
        "Int", "Bool", "String", "ERROR"
    };

    std::map<std::string, Symbolic::Type>::iterator iter = mTypemap.find(source.getIdentifier());

    if (iter != mTypemap.end()) {
        // type already recorded, update type info
        iter->second = iter->second == type ? type : Symbolic::TYPEERROR;
    } else {
        // type not recorded before, output definition and store type
        mTypemap.insert(std::pair<std::string, Symbolic::Type>(source.getIdentifier(), type));

        mOutput << "(declare-const " << Z3STRConstraintWriter::encodeIdentifier(source.getIdentifier()) << " " << typeStrings[type] << ")\n";
    }

}

bool Z3STRConstraintWriter::checkType(Symbolic::Type expected) {
    return mExpressionType == expected;
}

std::string Z3STRConstraintWriter::stringfindreplace(const std::string& string,
                                                     const std::string& search,
                                                     const std::string& replace) {
    std::string newString = string;

    size_t start_pos = 0;
    while ((start_pos = newString.find(search, start_pos)) != std::string::npos) {
        newString.replace(start_pos, search.length(), replace);
        start_pos += replace.length();
    }

    return newString;
}

/**
 * Z3 don't support "_" in identifiers, thus they should be encoded (done internally
 * when writing constraints) end decoded (when reading the constraints).
 */
std::string Z3STRConstraintWriter::encodeIdentifier(const std::string& identifier) {

    std::string SEARCH = "_";
    std::string REPLACE = "QQQ";

    return Z3STRConstraintWriter::stringfindreplace(identifier, SEARCH, REPLACE);
}

std::string Z3STRConstraintWriter::decodeIdentifier(const std::string& identifier) {

    std::string SEARCH = "QQQ";
    std::string REPLACE = "_";

    return Z3STRConstraintWriter::stringfindreplace(identifier, SEARCH, REPLACE);
}


}
