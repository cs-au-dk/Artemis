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
#include <math.h>

#include <QDebug>

#include "util/loggingutil.h"

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

/** Symbolic Integer/String/Boolean **/


void Z3STRConstraintWriter::visit(Symbolic::SymbolicInteger* symbolicinteger)
{
    // Forces this symbolic value to be of type mExpressionType
    recordAndEmitType(symbolicinteger->getSource(), mExpressionType);

    // Note, we skip the mExpressionType check since we automatically emit a symbolic
    // value of exactly this type (and if not we have raised an error.

    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicinteger->getSource().getIdentifier());
}

void Z3STRConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring)
{
    // Forces this symbolic value to be of type mExpressionType
    recordAndEmitType(symbolicstring->getSource(), mExpressionType);

    // Note, we skip the mExpressionType check since we automatically emit a symbolic
    // value of exactly this type (and if not we have raised an error.

    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicstring->getSource().getIdentifier());
}

void Z3STRConstraintWriter::visit(Symbolic::SymbolicBoolean* symbolicboolean)
{
    // Forces this symbolic value to be of type mExpressionType
    recordAndEmitType(symbolicboolean->getSource(), mExpressionType);

    // Note, we skip the mExpressionType check since we automatically emit a symbolic
    // value of exactly this type (and if not we have raised an error.

    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicboolean->getSource().getIdentifier());
}

/** Constant Integer/String/Boolean **/


void Z3STRConstraintWriter::visit(Symbolic::ConstantInteger* constantinteger)
{
    /**
     * Note! We convert the double into an integer in some cases since we do not support
     * writing constraints on real values right now.
     */

    std::ostringstream doubleToInt;
    if (isnan(constantinteger->getValue())) {
        doubleToInt << "nan";
    } else {
        doubleToInt << (int)constantinteger->getValue();
    }

    std::ostringstream strs;

    switch (mExpressionType) {
    case Symbolic::INT:
        strs << doubleToInt.str();
        break;
    case Symbolic::STRING:
        strs << "\"" << doubleToInt.str() << "\"";
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

    // negative number fix, the correct syntax is (- 1) not -1
    if (mExpressionBuffer.find_first_of("-") == 0) {
        mExpressionBuffer = "(- " + mExpressionBuffer.substr(1) + ")";
    }

    if (mExpressionBuffer.find("nan") != std::string::npos) {
        mError = true;
        mErrorReason = "Unsupported constraint using NaN constant";
    }
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

/** Coercion NOOP **/

void Z3STRConstraintWriter::visit(Symbolic::IntegerCoercion* integercoercion)
{
    assert(checkType(Symbolic::INT));
    integercoercion->getExpression()->accept(this);
}

void Z3STRConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion)
{
    assert(checkType(Symbolic::STRING));
    stringcoercion->getExpression()->accept(this);
}

void Z3STRConstraintWriter::visit(Symbolic::BooleanCoercion* booleancoercion)
{
    assert(checkType(Symbolic::BOOL ));
    booleancoercion->getExpression()->accept(this);
}


/** Binary Operations **/

void Z3STRConstraintWriter::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation)
{
    static const char* op[] = {
        "(+ ", "(- ", "(* ", "(div ", "(= ", "(= (= ", "(<= ", "(< ", "(>= ", "(> ", "(mod ", "(= (= ", "(= "
    };

    static const char* opclose[] = {
        ")", ")", ")", ")", ")", ") false)", ")", ")", ")", ")", ")", ") false)", ")"
    };

    Symbolic::Type expectedType = mExpressionType;

    mExpressionType = Symbolic::INT;
    integerbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;

    mExpressionType = Symbolic::INT;
    integerbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;

    std::ostringstream strs;
    strs << op[integerbinaryoperation->getOp()] << lhs << " " << rhs << opclose[integerbinaryoperation->getOp()];

    coercetype(opGetType(integerbinaryoperation->getOp()), expectedType, strs.str());
}

void Z3STRConstraintWriter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation)
{
    static const char* op[] = {
        "(Concat ", "(= ", "(= (= ", "_", "_", "_", "_", "(= ", "(= (= "
    };

    static const char* opclose[] = {
        ")", ")", ") false)", "_", "_", "_", "_", ")", ") false)"
    };

    switch (stringbinaryoperation->getOp()) {
    case Symbolic::STRING_GEQ:
    case Symbolic::STRING_GT:
    case Symbolic::STRING_LEQ:
    case Symbolic::STRING_LT:
        mError = true;
        mErrorReason = "Unsupported operation on strings";
        return;
    default:
        break;
    }

    Symbolic::Type expectedType = mExpressionType;

    mExpressionType = Symbolic::STRING;
    stringbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;

    mExpressionType = Symbolic::STRING;
    stringbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;

    std::ostringstream strs;
    strs << op[stringbinaryoperation->getOp()] << lhs << " " << rhs << opclose[stringbinaryoperation->getOp()];

    coercetype(opGetType(stringbinaryoperation->getOp()), expectedType, strs.str());
}

void Z3STRConstraintWriter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation)
{
    static const char* op[] = {
        "(= ", "(= (= ", "(= ", "(! (= "
    };

    static const char* opclose[] = {
        ")", ") false)", ")", "))"
    };

    Symbolic::Type expectedType = mExpressionType;

    mExpressionType = Symbolic::BOOL;
    booleanbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;

    mExpressionType = Symbolic::BOOL;
    booleanbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;

    std::ostringstream strs;
    strs << op[booleanbinaryoperation->getOp()] << lhs << " " << rhs << opclose[booleanbinaryoperation->getOp()];

    coercetype(opGetType(booleanbinaryoperation->getOp()), expectedType, strs.str());
}

/** Other Operations **/

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

void Z3STRConstraintWriter::visit(Symbolic::StringLength* stringlength)
{
    Symbolic::Type expectedType = mExpressionType;

    mExpressionType = Symbolic::STRING;
    stringlength->getString()->accept(this);

    std::ostringstream strs;
    strs << "(Length " << mExpressionBuffer << ")";

    coercetype(Symbolic::INT, expectedType, strs.str());
}


/** Utility **/


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

void Z3STRConstraintWriter::coercetype(Symbolic::Type from,
                                              Symbolic::Type to,
                                              std::string expression)
{

    switch (from) {
    case Symbolic::INT:

        switch (to) {
        case Symbolic::INT:
            mExpressionBuffer = expression; // No coercion
            break;

        case Symbolic::STRING:
            mError = true;
            mErrorReason = "Unsupported type coercion from INT to STRING";
            break;

        case Symbolic::BOOL:
            mExpressionBuffer = "(= (= " + expression + " 0) false)";
            break;

        default:
            mError = true;
            mErrorReason = "Unsupported type coercion from INT to UNKNOWN";
            break;
        }

        break;


    case Symbolic::STRING:

        switch (to) {
        case Symbolic::INT:
            mError = true;
            mErrorReason = "Unsupported type coercion from STRING to INT";
            break;

        case Symbolic::STRING:
            mExpressionBuffer = expression; // No coercion
            break;

        case Symbolic::BOOL:
            mExpressionBuffer = "(= (= " + expression + " \"\") false)";
            break;

        default:
            mError = true;
            mErrorReason = "Unsupported type coercion from STRING to UNKNOWN";
            break;
        }

        break;


    case Symbolic::BOOL:

        switch (to) {
        case Symbolic::INT:
            mExpressionBuffer = "(if " + expression + " 1 0)";
            break;

        case Symbolic::STRING:
            mExpressionBuffer = "(if " + expression + " \"true\" \"false\")";
            break;

        case Symbolic::BOOL:
            mExpressionBuffer = expression; // No coercion
            break;

        default:
            mError = true;
            mErrorReason = "Unsupported type coercion from INT to UNKNOWN";
            break;
        }

        break;

    default:
        mError = true;
        mErrorReason = "Unsupported type coercion from UNKNOWN to UNKNOWN";
        break;
    }

}


}
