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

#include "cvc4regexcompiler.h"

#include "cvc4.h"

namespace artemis
{

std::string OBJECT_NULL = "false";
std::string OBJECT_NOT_NULL = "true";

CVC4ConstraintWriter::CVC4ConstraintWriter()
    : SMTConstraintWriter()
{

}

void CVC4ConstraintWriter::preVisitPathConditionsHook()
{
    mOutput << "(set-logic UFSLIA)" << std::endl;
    mOutput << "(set-option :produce-models true)" << std::endl;
    mOutput << "(set-option :strings-exp true)" << std::endl;
    mOutput << "(set-option :strings-fmf true)" << std::endl;
    //mOutput << "(set-option :fmf-bound-int true)" << std::endl;
    //mOutput << "(set-option :finite-model-find true)" << std::endl;
    mOutput << std::endl;
}

void CVC4ConstraintWriter::postVisitPathConditionsHook()
{
    mOutput << "\n";
    mOutput << "(check-sat)\n";
    mOutput << "(get-model)\n";
}

void CVC4ConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring, void* args)
{
    // If we are coercing from an input (string) to an integer, then this is a special case.
    // Instead of returning a symbolic string (which would raise an error) we just silently ignore the coercion and record
    // the variable as an integer instead of a string.
    if (args != NULL) {

        CoercionPromise* promise = (CoercionPromise*)args;

        if (promise->coerceTo == Symbolic::INT) {
            promise->isCoerced = true;

            recordAndEmitType(symbolicstring->getSource(), Symbolic::INT);
            mExpressionBuffer = SMTConstraintWriter::encodeIdentifier(symbolicstring->getSource().getIdentifier());
            mExpressionType = Symbolic::INT;

            return;

        }
    }

    // Checks this symbolic value is of type STRING and raises an error otherwise.
    recordAndEmitType(symbolicstring->getSource(), Symbolic::STRING);

    mExpressionBuffer = SMTConstraintWriter::encodeIdentifier(symbolicstring->getSource().getIdentifier());
    mExpressionType = Symbolic::STRING;
}

void CVC4ConstraintWriter::visit(Symbolic::ConstantString* constantstring, void* args)
{
    std::ostringstream strs;

    strs << "\"" << *constantstring->getValue() << "\"";

    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::STRING;
}

void CVC4ConstraintWriter::visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args)
{
    static const char* op[] = {
        "(str.++ ", "(= ", "(= (= ", "_", "_", "_", "_", "(= ", "(= (= "
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

void CVC4ConstraintWriter::visit(Symbolic::StringCoercion* stringcoercion, void* args)
{
    CoercionPromise promise(Symbolic::STRING);
    stringcoercion->getExpression()->accept(this);

    if (!promise.isCoerced) {
        coercetype(mExpressionType, Symbolic::STRING, mExpressionBuffer); // Sets mExpressionBuffer and Type.
    }
}

void CVC4ConstraintWriter::visit(Symbolic::StringCharAt* stringcharat, void* arg)
{
    stringcharat->getSource()->accept(this);
    if(!checkType(Symbolic::STRING)){
        error("String char at operation on non-string");
        return;
    }

    // CVC4 requires the length of mExpressionBuffer to be at least getPosition+1.
    mOutput << "(assert (> (str.len " << mExpressionBuffer << ") " << stringcharat->getPosition() << "))" << std::endl;

    std::ostringstream strs;
    strs << "(str.at " << mExpressionBuffer << " " << stringcharat->getPosition() << ")";
    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::STRING;
}

void CVC4ConstraintWriter::visit(Symbolic::StringRegexReplace* obj, void* args)
{
    /**
      * TODO:
      *
      * Support the negative case.
      */

    obj->getSource()->accept(this, args); // send args through, allow local coercions

    // Detect if there was a local coercion performed, in which case this regex replace should be ignored.
    if (isSuccessfulCoercion(args)) {
        // Let mExpressionBuffer and type flow through as-is.
        // StringRegexReplace is completely transparent to successful CoercionPromises.
        return;
    }

    // Otherwise, we expect a string subexpression.
    if(!checkType(Symbolic::STRING)){
        error("StringRegexReplace operation on non-string");
        return;
    }

    // special case input filtering (filters matching X and replacing with "")
    if (obj->getReplace()->compare("") == 0) {

        // ignore the filter
        mExpressionBuffer = mExpressionBuffer;
        mExpressionType = mExpressionType;

        statistics()->accumulate("Concolic::Solver::RegexSuccessfullyTranslated", 1);

        return;
    }

    std::string pre, match, post;
    this->helperRegexMatchPositive(*obj->getRegexpattern(), mExpressionBuffer, &pre, &match, &post);

    std::stringstream out;

    if (!pre.empty() || !post.empty()) {
        out << "(str.++ " << pre << " \"" << *obj->getReplace() << "\" " << post << ")";
    } else {
        out << "\"" << *obj->getReplace() << "\"";
    }

    mExpressionBuffer = out.str();
    mExpressionType = Symbolic::STRING;
}

void CVC4ConstraintWriter::visit(Symbolic::StringReplace* replace, void* args)
{
    replace->getSource()->accept(this, args); // send args through, allow local coercions

    // Detect if there was a local coercion performed, in which case this regex replace should be ignored.
    if (isSuccessfulCoercion(args)) {
        // Let mExpressionBuffer and type flow through as-is.
        // StringReplace is completely transparent to successful CoercionPromises.
        return;
    }

    // Otherwise, we expect a string subexpression.
    if(!checkType(Symbolic::STRING)){
        error("String replace operation on non-string");
        return;
    }

    std::stringstream str;
    str << "(str.replace " << mExpressionBuffer << " " << "\"" << *replace->getPattern() << "\" \"" << *replace->getReplace() << "\")";

    mExpressionBuffer = str.str();
    mExpressionType = Symbolic::STRING;
}

/**
 * Used by
 *
 * regex.prototype.test
 */
void CVC4ConstraintWriter::visit(Symbolic::StringRegexSubmatch* obj, void* args)
{
    obj->getSource()->accept(this);

    if(!checkType(Symbolic::STRING)){
        error("String char at operation on non-string");
        return;
    }

    std::string match = "ERROR";
    this->helperRegexTest(*obj->getRegexpattern(), mExpressionBuffer, &match);

    mExpressionBuffer = match;
    mExpressionType = Symbolic::BOOL;
}

void CVC4ConstraintWriter::visit(Symbolic::StringRegexSubmatchIndex* obj, void* args)
{
    obj->getSource()->accept(this);

    if(!checkType(Symbolic::STRING)){
        error("String submatch index operation on non-string");
        return;
    }

    std::string pre, match, post;
    this->helperRegexMatchPositive(*obj->getRegexpattern(), mExpressionBuffer, &pre, &match, &post);

    if (pre.empty()) {
        mExpressionBuffer = "0";
    } else {
        std::ostringstream out;
        out << "(str.len " << pre << ")";
        mExpressionBuffer = out.str();
    }

    mExpressionType = Symbolic::INT;

}

void CVC4ConstraintWriter::visit(Symbolic::StringRegexSubmatchArray* exp, void* arg)
{
    /**
      * TODO
      *
      * Add proper support for inspecting submatches (group 0...n)
      * - Accessing group 0 returns the source string, and not the match
      * - Accessing group 1...n throws an error
      *
      * A proper implementation will use helperRegexMatch (adds support for
      * group 0) and extends it to support sub matches (group 1...n).
      *
      */

    exp->getSource()->accept(this);

    if(!checkType(Symbolic::STRING)){
        error("String regex submation operation on non-string");
        return;
    }

    if (m_singletonCompilations.find(exp->getIdentifier()) == m_singletonCompilations.end()) {
        m_singletonCompilations.insert(exp->getIdentifier());

        std::string match = "ERROR";
        this->helperRegexTest(*exp->getRegexpattern(), mExpressionBuffer, &match);

        // Match
        std::stringstream matchIdResult;
        matchIdResult << "rs" << exp->getIdentifier() << "RESULT";

        this->emitConst(matchIdResult.str(), Symbolic::OBJECT);
        mOutput << "(assert (= " << matchIdResult.str() << " " << match << "))" << std::endl;

        // Index0
        std::stringstream matchIdIndex0;
        matchIdIndex0 << "rs" << exp->getIdentifier() << "INDEX0";

        this->emitConst(matchIdIndex0.str(), Symbolic::STRING);
        mOutput << "(assert (= " << matchIdIndex0.str() << " " << mExpressionBuffer << "))" << std::endl;
    }

    mExpressionType = Symbolic::OBJECT;

}

void CVC4ConstraintWriter::visit(Symbolic::StringRegexSubmatchArrayAt* exp, void* arg)
{
    exp->getMatch()->accept(this);

    if(!checkType(Symbolic::OBJECT)){
        error("Array match operation (@) on non-object");
        return;
    }

    if (exp->getGroup() != 0) {
        error("Array match operation does not support accessing groups > 0");
        return;
    }

    std::stringstream matchIdIndex0;
    matchIdIndex0 << "rs" << exp->getMatch()->getIdentifier() << "INDEX0";

    mExpressionBuffer = matchIdIndex0.str();
    mExpressionType = Symbolic::OBJECT;
}

void CVC4ConstraintWriter::visit(Symbolic::StringRegexSubmatchArrayMatch* exp, void* arg)
{
    exp->getMatch()->accept(this);

    if(!checkType(Symbolic::OBJECT)){
        error("Array match operation (match value) on non-object");
        return;
    }

    std::stringstream matchIdResult;
    matchIdResult << "rs" << exp->getMatch()->getIdentifier() << "RESULT";

    mExpressionBuffer = matchIdResult.str();
    mExpressionType = Symbolic::OBJECT;
}

void CVC4ConstraintWriter::visit(Symbolic::ConstantObject* obj, void* arg)
{
    mExpressionType = Symbolic::OBJECT;
    mExpressionBuffer = obj->getIsnull() ? OBJECT_NULL : OBJECT_NOT_NULL;
}

void CVC4ConstraintWriter::visit(Symbolic::ObjectBinaryOperation* obj, void* arg)
{
    static const char* op[] = {
        "(= ", "(= (= "
    };

    static const char* opclose[] = {
        ")", ") false)"
    };

    obj->getLhs()->accept(this);
    std::string lhs = mExpressionBuffer;
    if(!checkType(Symbolic::OBJECT)){
        error("Object operation with incorrectly typed LHS");
        return;
    }

    obj->getRhs()->accept(this);
    std::string rhs = mExpressionBuffer;
    if(!checkType(Symbolic::OBJECT)){
        error("Object operation with incorrectly typed RHS");
        return;
    }

    std::ostringstream strs;
    strs << op[obj->getOp()] << lhs << " " << rhs << opclose[obj->getOp()];
    mExpressionBuffer = strs.str();
    mExpressionType = opGetType(obj->getOp());
}

void CVC4ConstraintWriter::visit(Symbolic::StringLength* stringlength, void* args)
{
    stringlength->getString()->accept(this);
    if(!checkType(Symbolic::STRING)){
        error("String length operation on non-string");
        return;
    }

    std::ostringstream strs;
    strs << "(str.len " << mExpressionBuffer << ")";
    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::INT;
}

void CVC4ConstraintWriter::helperRegexTest(const std::string& regex, const std::string& expression,
                                           std::string* outMatch)
{
    bool bol, eol = false;
    std::string cvc4regex;

    try {
        cvc4regex = CVC4RegexCompiler::compile(regex, bol, eol);
        mOutput << "; Regex compiler: " << regex << " -> " << cvc4regex << std::endl;

    } catch (CVC4RegexCompilerException ex) {
        std::stringstream err;
        err << "The CVC4RegexCompiler failed when compiling the regex " << regex << " with the error message: " << ex.what();
        error(err.str());
        return;
    }

    std::stringstream out;
    out << "(str.in.re " << expression;

    if (!bol || !eol) {
        out << " (re.++";
    }

    if (!bol) {
        out << " (re.* re.allchar)";
    }

    out << " " << cvc4regex;

    if (!eol) {
        out << " (re.* re.allchar)";
    }

    if (!bol || !eol) {
        out << ")";
    }

    out << ")";

    *outMatch = out.str();
}

void CVC4ConstraintWriter::helperRegexMatchPositive(const std::string& regex, const std::string& expression,
                                                    std::string* outPre, std::string* outMatch, std::string* outPost)
{
    /**
     * TODO:
     *
     * Add support for the negative version of helperRegexMatch.
     *
     */

    // Compile regex

    bool bol, eol = false;
    std::string cvc4regex;

    try {
        cvc4regex = CVC4RegexCompiler::compile(regex, bol, eol);
        mOutput << "; Regex compiler: " << regex << " -> " << cvc4regex << std::endl;

    } catch (CVC4RegexCompilerException ex) {
        std::stringstream err;
        err << "The CVC4RegexCompiler failed when compiling the regex " << regex << " with the error message: " << ex.what();
        error(err.str());
        return;
    }

    // Constraints (optimized for the positive case)

    if (bol && eol) {
        *outPre = "";
        *outMatch = expression;
        *outPost = "";

    } else if (bol) {
        std::string match = this->emitAndReturnNewTemporary(Symbolic::STRING);
        std::string post = this->emitAndReturnNewTemporary(Symbolic::STRING);

        mOutput << "(assert (= " << expression << " (str.++ " << match << " " << post << ")))" << std::endl;

        *outPre = "";
        *outMatch = match;
        *outPost = post;

    } else if (eol) {
        std::string pre = this->emitAndReturnNewTemporary(Symbolic::STRING);
        std::string match = this->emitAndReturnNewTemporary(Symbolic::STRING);

        mOutput << "(assert (= " << expression << " (str.++ " << pre << " " << match << ")))" << std::endl;

        *outPre = pre;
        *outMatch = match;
        *outPost = "";

    } else {
        std::string pre = this->emitAndReturnNewTemporary(Symbolic::STRING);
        std::string match = this->emitAndReturnNewTemporary(Symbolic::STRING);
        std::string post = this->emitAndReturnNewTemporary(Symbolic::STRING);

        mOutput << "(assert (= " << expression << " (str.++ " << pre << " " << match << " " << post << ")))" << std::endl;

        *outPre = pre;
        *outMatch = match;
        *outPost = post;
    }

    mOutput << "(assert (str.in.re " << *outMatch << " " << cvc4regex << "))" << std::endl;
}

}
