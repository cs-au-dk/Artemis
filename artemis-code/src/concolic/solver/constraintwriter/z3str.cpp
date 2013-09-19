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
#include <QDateTime>

#include "util/loggingutil.h"

#include "z3str.h"

#include "JavaScriptCore/symbolic/expression/symbolicstring.cpp" // To allow the dynamic_cast type checking.

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
    mConstriantLog.open("/tmp/z3constraintlog", std::ofstream::out | std::ofstream::app);

    mConstriantLog << "********************************************************************************\n";
    mConstriantLog << "Wrote Constraint at " << QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss").toStdString() << "\n";
    mConstriantLog << "\n";

    for (uint i = 0; i < pathCondition->size(); i++) {

        pathCondition->get(i).first->accept(this);
        if(!checkType(Symbolic::BOOL) && !checkType(Symbolic::TYPEERROR)){
            error("Writing the PC did not result in a boolean constraint");
        }

        mOutput << "(assert (= " << mExpressionBuffer;
        mOutput << (pathCondition->get(i).second ? " true" : " false");
        mOutput << "))\n";

        mConstriantLog << "(assert (= " << mExpressionBuffer;
        mConstriantLog << (pathCondition->get(i).second ? " true" : " false");
        mConstriantLog << "))\n";

    }

    mConstriantLog << "\n";

    mOutput.close();

    if (mError) {
        std::string error = std::string("Artemis is unable generate constraints - ") + mErrorReason + ".";
        Log::warning(error);
        mConstriantLog << error << std::endl;
        return false;
    }

    for (std::map<std::string, Symbolic::Type>::iterator iter = mTypemap.begin(); iter != mTypemap.end(); iter++) {
        if (iter->second == Symbolic::TYPEERROR) {
            Log::warning("Artemis is unable generate constraints - a type-error was found.");
            mConstriantLog << "Artemis is unable generate constraints - a type-error was found." << std::endl;
            return false;
        }
    }

    mConstriantLog.close();

    return true;
}

/** Symbolic Integer/String/Boolean **/


//N.B. This will not currently be present in any of our PCs.
void Z3STRConstraintWriter::visit(Symbolic::SymbolicInteger* symbolicinteger)
{
    // Checks this symbolic value is of type INT and raises an error otherwise.
    recordAndEmitType(symbolicinteger->getSource(), Symbolic::INT);

    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicinteger->getSource().getIdentifier());
    mExpressionType = Symbolic::INT;
}

void Z3STRConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring)
{
    // Checks this symbolic value is of type STRING and raises an error otherwise.
    recordAndEmitType(symbolicstring->getSource(), Symbolic::STRING);

    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicstring->getSource().getIdentifier());
    mExpressionType = Symbolic::STRING;
}

//N.B. This will not currently be present in any of our PCs.
void Z3STRConstraintWriter::visit(Symbolic::SymbolicBoolean* symbolicboolean)
{
    // Checks this symbolic value is of type BOOL and raises an error otherwise.
    recordAndEmitType(symbolicboolean->getSource(), Symbolic::BOOL);

    mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicboolean->getSource().getIdentifier());
    mExpressionType = Symbolic::BOOL;
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
    strs << doubleToInt.str();

    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::INT;

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

    strs << "\"" << *constantstring->getValue() << "\"";

    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::STRING;
}

void Z3STRConstraintWriter::visit(Symbolic::ConstantBoolean* constantboolean)
{
    std::ostringstream strs;

    strs << (constantboolean->getValue() == true ? "true" : "false");

    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::BOOL;
}

/** Coercion **/

void Z3STRConstraintWriter::visit(Symbolic::IntegerCoercion* integercoercion)
{
    // If we are coercing from an input (string) to an integer, then this is a special case.
    // Instead of calling coerceType() (which would raise an error) we just silently ignore the coercion and record
    // the variable as an integer instead of a string.
    Symbolic::Expression* coercedexpression = integercoercion->getExpression();
    Symbolic::SymbolicString* symbolicstring = dynamic_cast<Symbolic::SymbolicString*>(coercedexpression);
    if(symbolicstring){
        // Instead of calling the visitor again on the child (which marks this input as a string), we handle it here
        // and mark it as an integer directly, ignoring the coercion.
        recordAndEmitType(symbolicstring->getSource(), Symbolic::INT);
        mExpressionBuffer = Z3STRConstraintWriter::encodeIdentifier(symbolicstring->getSource().getIdentifier());
        mExpressionType = Symbolic::INT;

        return;
    }

    integercoercion->getExpression()->accept(this);

    coercetype(mExpressionType, Symbolic::INT, mExpressionBuffer); // Sets mExpressionBuffer and Type.
}

void Z3STRConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion)
{
    stringcoercion->getExpression()->accept(this);

    coercetype(mExpressionType, Symbolic::STRING, mExpressionBuffer); // Sets mExpressionBuffer and Type.
}

void Z3STRConstraintWriter::visit(Symbolic::BooleanCoercion* booleancoercion)
{
    booleancoercion->getExpression()->accept(this);

    coercetype(mExpressionType, Symbolic::BOOL, mExpressionBuffer); // Sets mExpressionBuffer and Type.
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

    integerbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;
    if(!checkType(Symbolic::INT)){
        error("Integer operation with incorrectly typed LHS");
        return;
    }

    integerbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;
    if(!checkType(Symbolic::INT)){
        error("Integer operation with incorrectly typed RHS");
        return;
    }

    std::ostringstream strs;
    strs << op[integerbinaryoperation->getOp()] << lhs << " " << rhs << opclose[integerbinaryoperation->getOp()];
    mExpressionBuffer = strs.str();
    mExpressionType = opGetType(integerbinaryoperation->getOp());
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

    stringbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;
    if(!checkType(Symbolic::STRING)){
        error("String operation with incorrectly typed LHS");
        return;
    }

    stringbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;
    if(!checkType(Symbolic::STRING)){
        error("String operation with incorrectly typed RHS");
        return;
    }

    std::ostringstream strs;
    strs << op[stringbinaryoperation->getOp()] << lhs << " " << rhs << opclose[stringbinaryoperation->getOp()];
    mExpressionBuffer = strs.str();
    mExpressionType = opGetType(stringbinaryoperation->getOp());
}

void Z3STRConstraintWriter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation)
{
    static const char* op[] = {
        "(= ", "(= (= ", "(= ", "(! (= "
    };

    static const char* opclose[] = {
        ")", ") false)", ")", "))"
    };

    booleanbinaryoperation->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;
    if(!checkType(Symbolic::BOOL)){
        error("Boolean operation with incorrectly typed LHS");
        return;
    }

    booleanbinaryoperation->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;
    if(!checkType(Symbolic::BOOL)){
        error("Boolean operation with incorrectly typed RHS");
        return;
    }

    std::ostringstream strs;
    strs << op[booleanbinaryoperation->getOp()] << lhs << " " << rhs << opclose[booleanbinaryoperation->getOp()];
    mExpressionBuffer = strs.str();
    mExpressionType = opGetType(booleanbinaryoperation->getOp());
}

/** Other Operations **/

void Z3STRConstraintWriter::visit(Symbolic::StringRegexReplace*)
{
    error("Regex constraints not supported");
}

void Z3STRConstraintWriter::visit(Symbolic::StringReplace*)
{
    error("String replace constraints not supported");
}

void Z3STRConstraintWriter::visit(Symbolic::StringLength* stringlength)
{
    stringlength->getString()->accept(this);
    if(!checkType(Symbolic::STRING)){
        error("String length operation on non-string");
        return;
    }

    std::ostringstream strs;
    strs << "(Length " << mExpressionBuffer << ")";
    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::STRING;
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
        mConstriantLog << "(declare-const " << Z3STRConstraintWriter::encodeIdentifier(source.getIdentifier()) << " " << typeStrings[type] << ")\n";
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

void Z3STRConstraintWriter::error(std::string reason)
{
    mError = true;
    mErrorReason = reason;
    mExpressionBuffer = "ERROR";

    // TODO: Temporary.
    mConstriantLog << reason << std::endl;
}


/**
 * Z3 doesn't support "_" in identifiers, thus they should be encoded (done internally
 * when writing constraints) and decoded (when reading the constraints).
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
    mExpressionType = Symbolic::TYPEERROR;

    switch (from) {
    case Symbolic::INT:

        switch (to) {
        case Symbolic::INT:
            mExpressionBuffer = expression; // No coercion
            mExpressionType = Symbolic::INT;
            break;

        case Symbolic::STRING:
            mError = true;
            mErrorReason = "Unsupported type coercion from INT to STRING";
            break;

        case Symbolic::BOOL:
            mExpressionBuffer = "(= (= " + expression + " 0) false)";
            mExpressionType = Symbolic::BOOL;
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
            mExpressionType = Symbolic::STRING;
            break;

        case Symbolic::BOOL:
            mExpressionBuffer = "(= (= " + expression + " \"\") false)";
            mExpressionType = Symbolic::BOOL;
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
            mExpressionType = Symbolic::INT;
            break;

        case Symbolic::STRING:
            mExpressionBuffer = "(if " + expression + " \"true\" \"false\")";
            mExpressionType = Symbolic::STRING;
            break;

        case Symbolic::BOOL:
            mExpressionBuffer = expression; // No coercion
            mExpressionType = Symbolic::BOOL;
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
