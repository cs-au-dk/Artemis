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

#include "z3str.h"

namespace artemis
{

Z3STRConstraintWriter::Z3STRConstraintWriter()
    : SMTConstraintWriter()
{
}

std::string Z3STRConstraintWriter::ifLabel()
{
    return "if";
}

void Z3STRConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring, void* args)
{
    std::string name = symbolicstring->getSource().getIdentifier();

    // If we are coercing from an input (string) to an integer, then this is a special case.
    // Instead of returning a symbolic string (which would raise an error) we just silently ignore the coercion and
    // record the variable as an integer instead of a string.
    if(args != NULL) {

        CoercionPromise* promise = (CoercionPromise*)args;

        if (promise->coerceTo == Symbolic::INT) {
            promise->isCoerced = true;

            // Check this symbolic variable against the expected type STRING and add a coercion if necessary/possible.
            emitVariableAndAnyCoercion(name, Symbolic::INT); // Sets mExpressionBuffer and Type.
            return;
        }
    }

    // Check this symbolic variable against the expected type STRING and add a coercion if necessary/possible.
    emitVariableAndAnyCoercion(name, Symbolic::STRING); // Sets mExpressionBuffer and Type.
}

void Z3STRConstraintWriter::visit(Symbolic::ConstantString* constantstring, void* args)
{
    std::ostringstream strs;

    strs << "\"" << *constantstring->getValue() << "\"";

    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::STRING;
}

void Z3STRConstraintWriter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args)
{
    static const char* op[] = {
        "(Concat ", "(= ", "(= (= ", "_", "_", "_", "_", "(= ", "(= (= "
    };

    static const char* opclose[] = {
        ")", ")", ") false)", "_", "_", "_", "_", ")", ") false)"
    };

    switch (stringbinaryoperation->getOp()) {
    case Symbolic::CONCAT:
    case Symbolic::STRING_EQ:
    case Symbolic::STRING_NEQ:
    case Symbolic::STRING_SEQ:
    case Symbolic::STRING_SNEQ:
        break; // these are supported
    default:
        error("Unsupported operation on strings");
        return;
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

void Z3STRConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion, void* args)
{
    CoercionPromise promise(Symbolic::STRING);
    stringcoercion->getExpression()->accept(this, &promise);

    if (!promise.isCoerced) {
        coercetype(mExpressionType, Symbolic::STRING, mExpressionBuffer); // Sets mExpressionBuffer and Type.
    }
}

void Z3STRConstraintWriter::visit(Symbolic::StringRegexReplace* regex, void* args)
{
    // special case input filtering (filters matching X and replacing with "")
    if (regex->getReplace()->compare("") == 0) {

        // right now, only support a very limited number of whitespace filters

        bool replaceSpaces = regex->getRegexpattern()->compare("/ /g") == 0 ||
                regex->getRegexpattern()->compare("/ /") == 0;
        bool replaceNewlines = regex->getRegexpattern()->compare("/\\n/g") == 0 ||
                regex->getRegexpattern()->compare("/\\r/") == 0 ||
                regex->getRegexpattern()->compare("/\\r\\n/") == 0;

        if (replaceSpaces || replaceNewlines || true) { // TODO: Hack, always filter away these for now

            // args (a possible CoercionPromise) is sent through, making StringRegexReplace "transparent" to these
            // promises and allowing a coercion to be pushed through them if that is useful.
            regex->getSource()->accept(this, args);

            // You could use the following block to prevent certain characters to be used,
            // but this would be problematic wrt. possible coercions, so we just ignore these filtering regexes.

            //if(!checkType(Symbolic::STRING)){
            //    error("String regex operation on non-string");
            //    return;
            //}
            //
            //if(replaceSpaces){
            //    mOutput << "(assert (= (Contains " << mExpressionBuffer << " \" \") false))\n";
            //    mConstriantLog << "(assert (= (Contains " << mExpressionBuffer << " \" \") false))\n";
            //}

            // In fact the solver currently cannot return results which contain newlines,
            // so we can completely ignore the case of replaceNewlines.

            // to be explicit, we just let the parent buffer flow down
            mExpressionBuffer = mExpressionBuffer;
            mExpressionType = mExpressionType;

            statistics()->accumulate("Concolic::Solver::RegexSuccessfullyTranslated", 1);

            return;
        }

    }


    statistics()->accumulate("Concolic::Solver::RegexNotTranslated", 1);
    error("Regex constraints not supported");


}

void Z3STRConstraintWriter::visit(Symbolic::StringReplace* replace, void* args)
{
    // The args (a possible CoercionPromise) is sent through, making StringReplace "transparent" to these
    // promises and allowing a coercion to be pushed through them if that is useful.
    // However, this means we must be careful not to emit the StringReplace in cases where we havce managed to do a
    // successful coercion.
    replace->getSource()->accept(this, args);

    if(!checkType(Symbolic::STRING)){
        // If the returned type is non-string, then either we have successfully coerced an input or we have an error.

        // TODO: This optimisation is only valid in cases where the string replace is doing some cleaning-up which is
        // irrelevant to our injected values of the coerced type (e.g. stripping whitespace around ints).

        if(args != NULL) {

            CoercionPromise* promise = (CoercionPromise*)args;
            if(promise->isCoerced) {
                // We did a successful implicit coercion, so elide this StringReplace and let mExpressionBuffer and
                // Type flow down.
                mExpressionBuffer = mExpressionBuffer;
                mExpressionType = mExpressionType;
                return;
            }
        }

        error("String replace operation on non-string");
        return;
    }

    std::ostringstream strs;
    strs << "(Replace " << mExpressionBuffer << " \"" << *replace->getPattern() << "\" \"" << *replace->getReplace() << "\")";

    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::STRING;
}

void Z3STRConstraintWriter::visit(Symbolic::StringLength* stringlength, void* args)
{
    stringlength->getString()->accept(this);
    if(!checkType(Symbolic::STRING)){
        error("String length operation on non-string");
        return;
    }

    std::ostringstream strs;
    strs << "(Length " << mExpressionBuffer << ")";
    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::INT;
}

}
