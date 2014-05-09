/*
 * Copyright 2013 Aarhus University
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
#include "statistics/statsstorage.h"

#include "smt.h"

namespace artemis
{

SMTConstraintWriter::SMTConstraintWriter()
    : mExpressionType(Symbolic::TYPEERROR)
    , mError(false)
    , mNextTemporarySequence(0)
{
}

void SMTConstraintWriter::preVisitPathConditionsHook(QSet<QString> varsUsed)
{
}

void SMTConstraintWriter::postVisitPathConditionsHook()
{
}

std::string SMTConstraintWriter::ifLabel()
{
    return "ite";
}

bool SMTConstraintWriter::write(PathConditionPtr pathCondition, FormRestrictions formRestrictions, std::string outputFile)
{
    mError = false;

    mFormRestrictions = formRestrictions;

    mOutput.open(outputFile.data());

    QSet<QString> freeVars = pathCondition->freeVariables().keys().toSet();
    preVisitPathConditionsHook(freeVars);

    for (uint i = 0; i < pathCondition->size(); i++) {

        pathCondition->get(i).first->accept(this);
        if(!checkType(Symbolic::BOOL) && !checkType(Symbolic::TYPEERROR)){
            error("Writing the PC did not result in a boolean constraint");
        }

        mOutput << "(assert (= " << mExpressionBuffer;
        mOutput << (pathCondition->get(i).second ? " true" : " false");
        mOutput << "))\n";
    }

    postVisitPathConditionsHook();

    mOutput.close();

    if (mError) {
        return false;
    }

    for (std::map<std::string, Symbolic::Type>::iterator iter = mTypemap.begin(); iter != mTypemap.end(); iter++) {
        if (iter->second == Symbolic::TYPEERROR) {
            mErrorReason = "Artemis is unable generate constraints - a type-error was found.";
            return false;
        }
    }

    return true;
}

/** Symbolic Integer/String/Boolean **/


//N.B. This will not currently be present in any of our PCs.
void SMTConstraintWriter::visit(Symbolic::SymbolicInteger* symbolicinteger, void* args)
{
    // Checks this symbolic value is of type INT and raises an error otherwise.
    recordAndEmitType(symbolicinteger->getSource(), Symbolic::INT);

    mExpressionBuffer = SMTConstraintWriter::encodeIdentifier(symbolicinteger->getSource().getIdentifier());
    mExpressionType = Symbolic::INT;
}

void SMTConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring, void* args)
{
    error("NO SYMBOLIC STRING SUPPORT");
}

//N.B. This will not currently be present in any of our PCs.
void SMTConstraintWriter::visit(Symbolic::SymbolicBoolean* symbolicboolean, void* args)
{
    // Checks this symbolic value is of type BOOL and raises an error otherwise.
    recordAndEmitType(symbolicboolean->getSource(), Symbolic::BOOL);

    mExpressionBuffer = SMTConstraintWriter::encodeIdentifier(symbolicboolean->getSource().getIdentifier());
    mExpressionType = Symbolic::BOOL;
}

/** Constant Integer/String/Boolean **/


void SMTConstraintWriter::visit(Symbolic::ConstantInteger* constantinteger, void* args)
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
        error("Unsupported constraint using NaN constant");
    }
}

void SMTConstraintWriter::visit(Symbolic::ConstantString* constantstring, void* args)
{
    error("NO SYMBOLIC STRING SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::ConstantBoolean* constantboolean, void* args)
{
    std::ostringstream strs;

    strs << (constantboolean->getValue() == true ? "true" : "false");

    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::BOOL;
}

/** Coercion **/

void SMTConstraintWriter::visit(Symbolic::IntegerCoercion* integercoercion, void* args)
{
    CoercionPromise promise(Symbolic::INT);
    integercoercion->getExpression()->accept(this, &promise);

    if (!promise.isCoerced) {
        coercetype(mExpressionType, Symbolic::INT, mExpressionBuffer); // Sets mExpressionBuffer and Type.
    }
}

void SMTConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion, void* args)
{
    error("NO SYMBOLIC STRING SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::StringCharAt* stringcharat, void* arg)
{
    error("NO SYMBOLIC STRING SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::BooleanCoercion* booleancoercion, void* args)
{
    CoercionPromise promise(Symbolic::BOOL);
    booleancoercion->getExpression()->accept(this);

    if (!promise.isCoerced) {
        coercetype(mExpressionType, Symbolic::BOOL, mExpressionBuffer); // Sets mExpressionBuffer and Type.
    }
}


/** Binary Operations **/

void SMTConstraintWriter::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* args)
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

void SMTConstraintWriter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args)
{
    error("NO SYMBOLIC STRING SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* args)
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

void SMTConstraintWriter::visit(Symbolic::StringRegexSubmatch* submatch, void* args)
{
    error("NO SYMBOLIC STRING REGEX SUBMATCH SUPPORT");
}



/** Other Operations **/

void SMTConstraintWriter::visit(Symbolic::StringRegexReplace* regex, void* args)
{
    error("NO SYMBOLIC REGEX SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::StringReplace* replace, void* args)
{
    error("NO SYMBOLIC STRING REPLACE SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::StringRegexSubmatchArray* exp, void* arg)
{
    error("NO SYMBOLIC STRING REGEX SUBMATCH (ARRAY) SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::StringRegexSubmatchArrayAt* exp, void* arg)
{
    error("NO SYMBOLIC STRING REGEX SUBMATCH (ARRAY) SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::StringRegexSubmatchArrayMatch* exp, void* arg)
{
    error("NO SYMBOLIC STRING REGEX SUBMATCH (ARRAY) SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::ConstantObject* obj, void* arg)
{
    error("NO SYMBOLIC NULL/OBJECT SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::ObjectBinaryOperation* obj, void* arg)
{
    error("NO SYMBOLIC NULL/OBJECT SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::StringLength* stringlength, void* args)
{
    error("NO STRING LENGTH SUPPORT");
}

void SMTConstraintWriter::visit(Symbolic::StringRegexSubmatchIndex* submatchIndex, void* args)
{
    error("NO STRING REGEX SUBMATCH-INDEX SUPPORT");
}

/** Utility **/

std::string SMTConstraintWriter::stringfindreplace(const std::string& string,
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
 * Z3 doesn't support "_" in identifiers, thus they should be encoded before
 * writing constraints, and decoded before reading the constraints.
 */
std::string SMTConstraintWriter::encodeIdentifier(const std::string& identifier) {

    std::string SEARCH = "_";
    std::string REPLACE = "QQQ";

    return SMTConstraintWriter::stringfindreplace(identifier, SEARCH, REPLACE);
}

std::string SMTConstraintWriter::decodeIdentifier(const std::string& identifier) {

    std::string SEARCH = "QQQ";
    std::string REPLACE = "_";

    return SMTConstraintWriter::stringfindreplace(identifier, SEARCH, REPLACE);
}

/** Error handling **/

void SMTConstraintWriter::error(std::string reason)
{
    if(!mError){
        mError = true;
        mErrorReason = reason;
        mExpressionBuffer = "ERROR";
    }
}

/** Types **/

void SMTConstraintWriter::emitConst(const std::string& identifier, Symbolic::Type type)
{
    static const char* typeStrings[] = {
        "Int", "Bool", "String", "Bool", "ERROR"
    };

    mOutput << "(declare-const " << identifier << " " << typeStrings[type] << ")\n";
}

std::string SMTConstraintWriter::emitAndReturnNewTemporary(Symbolic::Type type)
{
    stringstream t;
    t << "TMP" << mNextTemporarySequence++;

    std::string temporaryName = t.str();

    emitConst(temporaryName, type);
    return temporaryName;
}

void SMTConstraintWriter::recordAndEmitType(const Symbolic::SymbolicSource& source, Symbolic::Type type)
{
    recordAndEmitType(source.getIdentifier(), type);
}

void SMTConstraintWriter::recordAndEmitType(const std::string& source, Symbolic::Type type)
{
    std::map<std::string, Symbolic::Type>::iterator iter = mTypemap.find(source);

    if (iter != mTypemap.end()) {
        // type already recorded, update type info
        iter->second = iter->second == type ? type : Symbolic::TYPEERROR;
    } else {
        // type not recorded before, output definition and store type
        mTypemap.insert(std::pair<std::string, Symbolic::Type>(source, type));
        emitConst(SMTConstraintWriter::encodeIdentifier(source), type);
    }

}

bool SMTConstraintWriter::checkType(Symbolic::Type expected) {
    return mExpressionType == expected;
}

void SMTConstraintWriter::coercetype(Symbolic::Type from,
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
            error("Unsupported type coercion from INT to STRING");
            break;

        case Symbolic::BOOL:
            mExpressionBuffer = "(= (= " + expression + " 0) false)";
            mExpressionType = Symbolic::BOOL;
            break;

        default:
            error("Unsupported type coercion from INT to UNKNOWN");
            break;
        }

        break;


    case Symbolic::STRING:

        switch (to) {
        case Symbolic::INT:
            error("Unsupported type coercion from STRING to INT");
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
            error("Unsupported type coercion from STRING to UNKNOWN");
            break;
        }

        break;


    case Symbolic::BOOL:

        switch (to) {
        case Symbolic::INT:
            mExpressionBuffer = "(" + ifLabel() + " " + expression + " 1 0)";
            mExpressionType = Symbolic::INT;
            break;

        case Symbolic::STRING:
            mExpressionBuffer = "("  + ifLabel() + " " + expression + " \"true\" \"false\")";
            mExpressionType = Symbolic::STRING;
            break;

        case Symbolic::BOOL:
            mExpressionBuffer = expression; // No coercion
            mExpressionType = Symbolic::BOOL;
            break;

        default:
            error("Unsupported type coercion from INT to UNKNOWN");
            break;
        }

        break;

    default:
        error("Unsupported type coercion from UNKNOWN to UNKNOWN");
        break;
    }

}


}
