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

#include "WebCore/dom/domsnapshot.h"
#include "model/domsnapshotstorage.h"

#include "cvc4.h"

namespace artemis
{

CVC4ConstraintWriter::CVC4ConstraintWriter(ConcolicBenchmarkFeatures disabledFeatures)
    : SMTConstraintWriter(disabledFeatures)
    , mTypeAnalysis(new CVC4TypeAnalysis())
{
}

bool CVC4ConstraintWriter::write(PathConditionPtr pathCondition, FormRestrictions formRestrictions, DomSnapshotStoragePtr domSnapshots, ReachablePathsConstraintSet reachablePaths, ReorderingConstraintInfoPtr reorderingInfo, std::string outputFile) {

    // pre analysis
    for (uint i = 0; i < pathCondition->size(); i++) {
        mTypeAnalysis->analyze(pathCondition->get(i).first);
    }
    mSawToLowerCase = false;
    mSawToUpperCase = false;

    // main visitor
    bool result = SMTConstraintWriter::write(pathCondition, formRestrictions, domSnapshots, reachablePaths, reorderingInfo, outputFile);
    // cleanup
    mTypeAnalysis->reset();
    mVisitedSymbolicObjects.clear();
    return result;
}

void CVC4ConstraintWriter::preVisitPathConditionsHook(QSet<QString> varsUsed)
{
    mOutput << "(set-logic UFSLIA)" << std::endl;
    mOutput << "(set-option :produce-models true)" << std::endl;
    mOutput << "(set-option :strings-exp true)" << std::endl;
    //mOutput << "(set-option :strings-fmf true)" << std::endl;
    //mOutput << "(set-option :fmf-bound-int true)" << std::endl;
    //mOutput << "(set-option :finite-model-find true)" << std::endl;
    mOutput << std::endl;

    // Only write the form restrictions which relate to variables which are actually used in the PC.
    QSet<QString> selectRestrictionIndexVariables;
    foreach(SelectRestriction sr, mFormRestrictions.first) {
        // TODO: Hack to guess the variable names, as in helperSelectRestriction().
        QString name = QString("SYM_IN_%1").arg(sr.variable);
        QString idxname = QString("SYM_IN_INT_%1").arg(sr.variable);
        selectRestrictionIndexVariables.insert(idxname);

        if(varsUsed.contains(name) && varsUsed.contains(idxname)) {
            if (!mDisabledFeatures.testFlag(SELECT_LINK_VALUE_INDEX)) {
                // Default behaviour: link value and index constraints.
                helperSelectRestriction(sr, VALUE_INDEX);
            } else {
                // Overridden behaviour: output both constraints separately.
                helperSelectRestriction(sr, VALUE_ONLY);
                helperSelectRestriction(sr, INDEX_ONLY);
            }
        } else if(varsUsed.contains(name)) {
            helperSelectRestriction(sr, VALUE_ONLY);
        } else if(varsUsed.contains(idxname)) {
            helperSelectRestriction(sr, INDEX_ONLY);
        }
        // else this select is not mentioned in the PC, so ignore.
    }
    foreach(RadioRestriction rr, mFormRestrictions.second) {
        QString name;
        bool variableMatch = false;
        foreach(QString var, rr.variables) {
            // TODO: Hack to guess the variable name in the constraint, as in helperRadioRestriction().
            name = QString("SYM_IN_BOOL_%1").arg(var);
            variableMatch = variableMatch || varsUsed.contains(name);
        }

        if(variableMatch) {
            helperRadioRestriction(rr);
        }
    }

    // Fallback sanity constraint for select indices (see b51f2e24) but in most (all?) cases it will be redundant to the main select restrictions.
    foreach (QString var, varsUsed) {
        if (var.contains("SYM_IN_INT") && !selectRestrictionIndexVariables.contains(var)) {
            Statistics::statistics()->accumulate("Concolic::Solver::IntegerVariableWithoutSelectRestriction", 1);
            // a select index, force positive numbers
            recordAndEmitType(var.toStdString(), Symbolic::INT);
            mOutput << "(assert (>= " << encodeIdentifier(var.toStdString()) << " 0))" << std::endl;
        }
    }
}

void CVC4ConstraintWriter::postVisitPathConditionsHook()
{
    emitDOMConstraints();

    mOutput << std::endl;
    mOutput << "(check-sat)" << std::endl;
    mOutput << "(get-model)" << std::endl;

    if(!mSuccessfulCoercions.empty()) {
        Statistics::statistics()->accumulate("Concolic::Solver::SuccessfulCoercionOptimisations", (int)mSuccessfulCoercions.size());
    }
}

bool CVC4ConstraintWriter::encodeUnderscore()
{
    return false;
}

void CVC4ConstraintWriter::visit(Symbolic::SymbolicString* symbolicstring, void* args)
{

    // If we are coercing from a string input to an integer downstream, it is safe to omit
    // the downstream coercion and return an integer here.
    if (!mDisabledFeatures.testFlag(CVC4_COERCION_OPT) && args != NULL) {

        CoercionPromise* promise = (CoercionPromise*)args;

        if (promise->coerceTo == Symbolic::INT &&
            mTypeAnalysis->hasUniqueConstraint(symbolicstring->getSource().getIdentifier(), CVC4TypeAnalysis::WEAK_INTEGER) &&
            FormFieldRestrictedValues::safeForIntegerCoercion(mFormRestrictions, QString::fromStdString(symbolicstring->getSource().getIdentifier())) ) {

            promise->isCoerced = true;

            recordAndEmitType(symbolicstring->getSource(), Symbolic::INT);
            mExpressionBuffer = encodeIdentifier(symbolicstring->getSource().getIdentifier());
            mExpressionType = Symbolic::INT;

            mSuccessfulCoercions.insert(symbolicstring->getSource().getIdentifier());
            Statistics::statistics()->accumulate("Concolic::Solver::StringIntCoercionOptimization", 1);

            return;
        }
    }

    // Checks this symbolic value is of type STRING and raises an error otherwise.
    recordAndEmitType(symbolicstring->getSource(), Symbolic::STRING);

    mExpressionBuffer = encodeIdentifier(symbolicstring->getSource().getIdentifier());
    mExpressionType = Symbolic::STRING;
}

void CVC4ConstraintWriter::visit(Symbolic::ConstantString* constantstring, void* args)
{
    std::ostringstream strs;

    strs << "\"" << CVC4RegexCompiler::escape(*constantstring->getValue()) << "\"";

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
    stringcoercion->getExpression()->accept(this, &promise);

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
    // Examples of whitespace filters
    // /^\s+|\s+$/g

    // special case input filtering (filters matching X and replacing with "")
    if (obj->getReplace()->compare("") == 0) {

        // In these "safe" replacements we send args through, allowing local coercion optimisations.
        obj->getSource()->accept(this, args);

        // ignore the filter (no-op)
        mExpressionBuffer = mExpressionBuffer;
        mExpressionType = mExpressionType;

        Statistics::statistics()->accumulate("Concolic::Solver::RegexSuccessfullyTranslated", 1);

        return;
    }

    // In the general case we do not pass args through and do not allow local coercion through StringRegexReplace.
    obj->getSource()->accept(this);

    if(!checkType(Symbolic::STRING)){
        error("StringRegexReplace operation on non-string");
        return;
    }

    std::string isMatch, pre, match, post;
    this->helperRegexMatch(*obj->getRegexpattern(), mExpressionBuffer, &isMatch, &pre, &match, &post);

    std::stringstream out;

    out << "(ite " << isMatch << " ";

    if (pre.compare("\"\"") == 0) pre = "";
    if (post.compare("\"\"") == 0) post = "";

    if (!pre.empty() || !post.empty()) {
        out << "(str.++ " << pre << " \"" << *obj->getReplace() << "\" " << post << ")";
    } else {
        out << "\"" << *obj->getReplace() << "\"";
    }

    out << " " << mExpressionBuffer << ")";

    mExpressionBuffer = out.str();
    mExpressionType = Symbolic::STRING;
}

void CVC4ConstraintWriter::visit(Symbolic::StringReplace* replace, void* args)
{
    // Currently we do not pass args through and therefore do not allow local coercion optimisations passing through
    // a StringReplace (as is done with StringRegexReplace in certain cases, see above).
    // The optimisation for StringRegexReplace improves jQuery support so it is common, but we have not seen the same
    // patterns with standard StringReplace.

    replace->getSource()->accept(this);

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

    std::string isMatch, pre, match, post;
    this->helperRegexMatch(*obj->getRegexpattern(), mExpressionBuffer, &isMatch, &pre, &match, &post);

    std::stringstream out;
    out << "(ite " << isMatch << " (str.len " << pre << ") (- 1))";

    mExpressionBuffer = out.str();
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

        // result symbol
        std::stringstream matchIdResult;
        matchIdResult << "rs" << exp->getIdentifier() << "RESULT";

        this->emitConst(matchIdResult.str(), Symbolic::OBJECT);

        // match => result != 0
        // !match => result == 0
        mOutput << "(assert (ite " << match << " (not (= " << matchIdResult.str() << " 0)) (= " << matchIdResult.str() << " 0) ))" << std::endl;

        // Index0 symbol
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
    mExpressionType = Symbolic::STRING;
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
    std::stringstream instanceIdentifier;
    instanceIdentifier << obj->getInstanceidentifier();

    mExpressionType = Symbolic::OBJECT;
    mExpressionBuffer = instanceIdentifier.str(); // 0 if the reference is null or undefined, otherwise its a number
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

void CVC4ConstraintWriter::visit(Symbolic::SymbolicObject* obj, void* arg)
{
    // If we are coercing from an object to a string downstream, it is safe to omit
    // the downstream coercion and return the "string" version of the object here.
    if (arg != NULL) {

        CoercionPromise* promise = (CoercionPromise*)arg;

        if (promise->coerceTo == Symbolic::STRING) {
            promise->isCoerced = true;

            std::stringstream ident;
            ident << obj->getSource().getIdentifier() << "__TOSTRING";

            recordAndEmitType(ident.str(), Symbolic::STRING);

            mUsedSymbolicObjectProperties[obj].insert("TOSTRING");

            mExpressionBuffer = encodeIdentifier(ident.str());
            mExpressionType = Symbolic::STRING;

            return;
        }

    }

    // Checks this symbolic value is of type OBJECT and raises an error otherwise.
    recordAndEmitType(obj->getSource(), Symbolic::OBJECT);

    mVisitedSymbolicObjects.insert(obj);

    mExpressionBuffer = encodeIdentifier(obj->getSource().getIdentifier());
    mExpressionType = Symbolic::OBJECT;
}

void CVC4ConstraintWriter::visit(Symbolic::SymbolicObjectPropertyString* obj, void* arg)
{
    obj->getObj()->accept(this);

    std::stringstream ident;
    ident << mExpressionBuffer << encodeIdentifier("__") << obj->getPropertyname();

    // Checks this symbolic value is of type OBJECT and raises an error otherwise.
    recordAndEmitType(ident.str(), Symbolic::STRING);

    mUsedSymbolicObjectProperties[obj->getObj()].insert(obj->getPropertyname());

    mExpressionBuffer = ident.str();
    mExpressionType = Symbolic::STRING;
}

void CVC4ConstraintWriter::visit(Symbolic::StringSubstring* obj, void* arg)
{
    obj->getSource()->accept(this);
    if(!checkType(Symbolic::STRING)){
        error("String substring operation on non-string type");
        return;
    }

    std::ostringstream i;
    std::ostringstream j;

    if (obj->getFrom() >= 0) {
        // fixed start index
        i << obj->getFrom();

        if (obj->getLength() >= 0) {
            // fixed length
            j << obj->getLength();

        } else {
            // unbounded
            j << emitAndReturnNewTemporary(Symbolic::INT);
            mOutput << "(assert (= " << j.str() << " (- (str.len " << mExpressionBuffer << ") " << obj->getFrom() << ")))" << std::endl;
        }

    } else {
        // relative start index to length

        i << emitAndReturnNewTemporary(Symbolic::INT);
        j << emitAndReturnNewTemporary(Symbolic::INT);

        //mOutput << "(assert (>= " << i.str() << " 0))" << std::endl; // TODO: This line seems uneccessary if we have the following?
        mOutput << "(assert (= " << i.str() << " (ite (>= (str.len " << mExpressionBuffer << ") " << (obj->getFrom() * -1) << ") " \
                   << "(- (str.len " << mExpressionBuffer << ") " << (obj->getFrom() * -1) << ") " \
                   << "0)))" << std::endl;

        if (obj->getLength() >= 0 && obj->getLength() < (obj->getFrom() * -1)) {
            // fixed length (i + length)
            mOutput << "(assert (= " << j.str() << " " << obj->getLength() << "))" << std::endl;

        } else {
            // unbounded or length longer than negative offset (length of source)
            mOutput << "(assert (= " << j.str() << " (- (str.len " << mExpressionBuffer << ") " << (obj->getFrom() * -1) << ")))" << std::endl;
        }
    }

    std::ostringstream strs;
    strs << "(str.substr " << mExpressionBuffer << " " << i.str() << " " << j.str() << ")";
    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::STRING;

}

void CVC4ConstraintWriter::visit(Symbolic::StringToLowerCase* stringtolowercase, void* arg)
{
    preambleAddToLowerCase();

    stringtolowercase->getSource()->accept(this);
    if(!checkType(Symbolic::STRING)){
        error("String toLowerCase operation on non-string");
        return;
    }

    // The SMT function str_tolowercase is "relational", so we must split the constraint here and introduce an intermediate variable.
    std::string intermediateName = emitAndReturnNewTemporary(Symbolic::STRING);

    // Output the constraint up to this point.
    std::ostringstream lowercase_constraint;
    lowercase_constraint << "(assert (str_tolowercase_bounded " << mExpressionBuffer << " " << intermediateName << "))";
    mOutput << lowercase_constraint.str() << "\n";

    // The returned expression is simply the new intermediate, which will be the lowercased version of mExpressionBuffer.
    mExpressionBuffer = intermediateName;
    mExpressionType = Symbolic::STRING;
}

void CVC4ConstraintWriter::visit(Symbolic::StringToUpperCase* stringtouppercase, void* arg)
{
    preambleAddToUpperCase();

    stringtouppercase->getSource()->accept(this);
    if(!checkType(Symbolic::STRING)){
        error("String toUpperCase operation on non-string");
        return;
    }

    // The SMT function str_touppercase is "relational", so we must split the constraint here and introduce an intermediate variable.
    std::string intermediateName = emitAndReturnNewTemporary(Symbolic::STRING);

    // Output the constraint up to this point.
    std::ostringstream uppercase_constraint;
    uppercase_constraint << "(assert (str_touppercase_bounded " << mExpressionBuffer << " " << intermediateName << "))";
    mOutput << uppercase_constraint.str() << "\n";

    // The returned expression is simply the new intermediate, which will be the uppercased version of mExpressionBuffer.
    mExpressionBuffer = intermediateName;
    mExpressionType = Symbolic::STRING;
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

void CVC4ConstraintWriter::visit(Symbolic::ObjectArrayIndexOf* obj, void* arg)
{
    std::string index = emitAndReturnNewTemporary(Symbolic::INT);
    std::stringstream output;
    output << "(assert (or";

    obj->getSearchelement()->accept(this);
    if(!checkType(Symbolic::OBJECT)){
        error("String array indexof operation on non-object");
        return;
    }

    std::string searchElementIdent = mExpressionBuffer;

    // Build hit cases

    std::list<Symbolic::Expression*> list = obj->getArray();
    std::list<Symbolic::Expression*>::iterator it = list.begin();
    unsigned int i = 0;
    for (; it != list.end(); ++it) {
        Symbolic::Expression* elm = (*it);

        elm->accept(this);
        if(!checkType(Symbolic::OBJECT)){
            error("String array indexof operation on non-object");
            return;
        }

        output << " (and (= " << index << " " << i << ") (= " << searchElementIdent << " " << mExpressionBuffer << "))";
        ++i;
    }

    // Build miss case

    output << " (and (= " << index << " (- 1))";

    it = list.begin();
    for (; it != list.end(); ++it) {
        Symbolic::Expression* elm = (*it);
        elm->accept(this);
        output << " (not (= " << searchElementIdent << " " << mExpressionBuffer << "))";
    }

    output << ")))";

    mOutput << output.str() << std::endl;
    mExpressionBuffer = index;
    mExpressionType = Symbolic::INT;
}

void CVC4ConstraintWriter::visit(Symbolic::StringIndexOf* obj, void* arg)
{
    obj->getSource()->accept(this);
    std::string source = mExpressionBuffer;
    if(!checkType(Symbolic::STRING)){
        error("String index of operation on non-string");
        return;
    }

    obj->getPattern()->accept(this);
    std::string pattern = mExpressionBuffer;
    if(!checkType(Symbolic::STRING)){
        error("String index of operation (pattern) on non-string");
        return;
    }

    obj->getOffset()->accept(this);
    std::string offset = mExpressionBuffer;
    if(!checkType(Symbolic::INT)){
        error("String index of operation (offset) on non-string");
        return;
    }

    std::ostringstream strs;
    strs << "(str.indexof " << source << " " << pattern << " " << offset << ")";
    mExpressionBuffer = strs.str();
    mExpressionType = Symbolic::INT;
}

/**
 * @brief CVC4ConstraintWriter::helperRegexTest
 * @param regex
 * @param expression
 * @param outMatch
 *
 * Returns a new boolean expression (outIsMatch) which evaluates to:
 * - true if regex matches a substring in expression, or
 * - false otherwise.
 *
 * outIsMatch is set to "ERROR" if an error occurs, and the internal error procedure is called.
 *
 */
void CVC4ConstraintWriter::helperRegexTest(const std::string& regex, const std::string& expression, std::string* outIsMatch)
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
        *outIsMatch = "ERROR";
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

    *outIsMatch = out.str();
}

/**
 * @brief CVC4ConstraintWriter::helperRegexMatch
 * @param regex
 * @param expression
 * @param outIsMatch
 * @param outPre
 * @param outMatch
 * @param outPost
 *
 * Returns a new boolean expression (outIsMatch) which evaluates to:
 * - true if regex matches a substring in expression, or
 * - false otherwise.
 *
 * If outIsMatch is true, then outMatch will contain the first occurrence of a match,
 * while outPre will contain the prefix of expression before outMatch and outPost will contain the suffix.
 *
 * out* is set to "ERROR" if an error occurs, and the internal error procedure is called.
 */
void CVC4ConstraintWriter::helperRegexMatch(const std::string& regex, const std::string& expression,
                                                    std::string* outIsMatch, std::string* outPre, std::string* outMatch, std::string* outPost)
{
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

        *outPre = *outMatch = *outPost = *outIsMatch = "ERROR";
        return;
    }

    // Constraints on match

    std::string isMatch;
    this->helperRegexTest(regex, expression, &isMatch);

    *outIsMatch = this->emitAndReturnNewTemporary(Symbolic::BOOL);
    mOutput << "(assert (= " << *outIsMatch << " " << isMatch << "))" << std::endl;

    // Constraints on outPre, outMatch, and outPost

    if (bol && eol) {
        *outPre = "\"\"";
        *outMatch = expression;
        *outPost = "\"\"";

    } else if (bol) {
        std::string match = this->emitAndReturnNewTemporary(Symbolic::STRING);
        std::string post = this->emitAndReturnNewTemporary(Symbolic::STRING);

        mOutput << "(assert (= " << expression << " (str.++ " << match << " " << post << ")))" << std::endl;

        *outPre = "\"\"";
        *outMatch = match;
        *outPost = post;

    } else if (eol) {
        std::string pre = this->emitAndReturnNewTemporary(Symbolic::STRING);
        std::string match = this->emitAndReturnNewTemporary(Symbolic::STRING);

        mOutput << "(assert (= " << expression << " (str.++ " << pre << " " << match << ")))" << std::endl;

        *outPre = pre;
        *outMatch = match;
        *outPost = "\"\"";

    } else {
        std::string pre = this->emitAndReturnNewTemporary(Symbolic::STRING);
        std::string match = this->emitAndReturnNewTemporary(Symbolic::STRING);
        std::string post = this->emitAndReturnNewTemporary(Symbolic::STRING);

        mOutput << "(assert (= " << expression << " (str.++ " << pre << " " << match << " " << post << ")))" << std::endl;

        *outPre = pre;
        *outMatch = match;
        *outPost = post;
    }

    mOutput << "(assert (=> " << *outIsMatch << " (and (str.in.re " << *outMatch << " " << cvc4regex << ") (not (str.in.re " << *outPre << " " << cvc4regex << ")))))" << std::endl;
}



void CVC4ConstraintWriter::helperSelectRestriction(SelectRestriction constraint, SelectConstraintType type)
{
    Statistics::statistics()->accumulate("Concolic::Solver::SelectDomConstraintsWritten", 1);
    if(type == VALUE_INDEX) {
        Statistics::statistics()->accumulate("Concolic::Solver::SelectConstraintsWithLinkedValueAndIndex", 1);
    }

    // TODO: Hack to guess the variable name in the constraint.
    QString name = QString("SYM_IN_%1").arg(constraint.variable);
    QString idxname = QString("SYM_IN_INT_%1").arg(constraint.variable);

    bool coerceToInt = false;
    if(type == VALUE_ONLY || type == VALUE_INDEX) {
        if (!mDisabledFeatures.testFlag(CVC4_COERCION_OPT) &&
                mTypeAnalysis->hasUniqueConstraint(name.toStdString(), CVC4TypeAnalysis::WEAK_INTEGER) &&
                FormFieldRestrictedValues::safeForIntegerCoercion(mFormRestrictions, name) ) {

            recordAndEmitType(name.toStdString(), Symbolic::INT, true);
            coerceToInt = true;

            mSuccessfulCoercions.insert(name.toStdString());
            Statistics::statistics()->accumulate("Concolic::Solver::StringIntCoercionOptimization", 1);

        } else {
            recordAndEmitType(name.toStdString(), Symbolic::STRING, true);
        }
    }

    if(type == INDEX_ONLY || type == VALUE_INDEX) {
        recordAndEmitType(idxname.toStdString(), Symbolic::INT, true);
    }

    // If the select is empty, assert some default values.
    if(constraint.values.isEmpty()) {
        std::stringstream idxconstraint;
        std::stringstream valueconstraint;

        valueconstraint << "(assert (= " << encodeIdentifier(name.toStdString(), true) << " \"\"))";
        idxconstraint << "(assert (= " << encodeIdentifier(idxname.toStdString(), true) << " (- 1)))";

        switch(type) {
        case VALUE_ONLY:
            mOutput << valueconstraint.str() << std::endl << std::endl;
            break;
        case INDEX_ONLY:
            mOutput << idxconstraint.str() << std::endl << std::endl;
            break;
        default:
            mOutput << idxconstraint.str()  << std::endl << valueconstraint.str() << std::endl << std::endl;
            break;
        }

        return;
    }

    mOutput << "(assert\n  (or\n";

    int idx = 0;
    foreach(QString value, constraint.values) {
        std::stringstream idxconstraint;
        std::stringstream valueconstraint;

        idxconstraint << "(= " << encodeIdentifier(idxname.toStdString(), true) << " " << idx << ")";

        if (coerceToInt) {
            valueconstraint << "(= " << encodeIdentifier(name.toStdString(), true) << " " << value.toStdString() << ")";
        } else {
            valueconstraint << "(= " << encodeIdentifier(name.toStdString(), true) << " \"" << value.toStdString() << "\")";
        }

        switch(type) {
        case VALUE_ONLY:
            mOutput << "    " << valueconstraint.str() << std::endl;
            break;
        case INDEX_ONLY:
            mOutput << "    " << idxconstraint.str() << std::endl;
            break;
        default:
            mOutput << "    (and " << idxconstraint.str() << " " << valueconstraint.str() << ")" << std::endl;
            break;
        }

        idx++;
    }

    mOutput << "  )\n)\n\n";
}

void CVC4ConstraintWriter::helperRadioRestriction(RadioRestriction constraint)
{
    Statistics::statistics()->accumulate("Concolic::Solver::RadioDomConstraintsWritten", 1);

    QString name;
    QList<QString> names;

    foreach(QString var, constraint.variables) {
        // TODO: Hack to guess the variable name in the constraint.
        name = QString("SYM_IN_BOOL_%1").arg(var);
        names.append(name);

        recordAndEmitType(name.toStdString(), Symbolic::BOOL, true);
    }

    mOutput << "(assert\n  (or\n";

    foreach(QString currentVar, names) {
        mOutput << "    (and ";

        foreach(QString var, names) {
            if(var == currentVar) {
                mOutput << encodeIdentifier(var.toStdString(), true) << " ";
            } else {
                mOutput << "(not " << encodeIdentifier(var.toStdString(), true) << ") ";
            }
        }

        mOutput << ")\n";
    }

    // If the radio button group is not always set, then it is possible to submit with all values false.
    if(!constraint.alwaysSet) {
        mOutput << "    (and ";
        foreach(QString var, names) {
            mOutput << "(not " << encodeIdentifier(var.toStdString(), true) << ") ";
        }
        mOutput << ")\n";
    }

    mOutput << "  )\n)\n\n";
}

void CVC4ConstraintWriter::preambleAddToLowerCase()
{
    if (mSawToLowerCase) {
        return;
    }
    mSawToLowerCase = true;

    int bound = 5;

    QString toLowerCase;
    toLowerCase += "(define-fun char_tolower ((ch String)) String\n";
    toLowerCase += "    (ite (= ch \"A\") \"a\"\n";
    toLowerCase += "    (ite (= ch \"B\") \"b\"\n";
    toLowerCase += "    (ite (= ch \"C\") \"c\"\n";
    toLowerCase += "    (ite (= ch \"D\") \"d\"\n";
    toLowerCase += "    (ite (= ch \"E\") \"e\"\n";
    toLowerCase += "    (ite (= ch \"F\") \"f\"\n";
    toLowerCase += "    (ite (= ch \"G\") \"g\"\n";
    toLowerCase += "    (ite (= ch \"H\") \"h\"\n";
    toLowerCase += "    (ite (= ch \"I\") \"i\"\n";
    toLowerCase += "    (ite (= ch \"J\") \"j\"\n";
    toLowerCase += "    (ite (= ch \"K\") \"k\"\n";
    toLowerCase += "    (ite (= ch \"L\") \"l\"\n";
    toLowerCase += "    (ite (= ch \"M\") \"m\"\n";
    toLowerCase += "    (ite (= ch \"N\") \"n\"\n";
    toLowerCase += "    (ite (= ch \"O\") \"o\"\n";
    toLowerCase += "    (ite (= ch \"P\") \"p\"\n";
    toLowerCase += "    (ite (= ch \"Q\") \"q\"\n";
    toLowerCase += "    (ite (= ch \"R\") \"r\"\n";
    toLowerCase += "    (ite (= ch \"S\") \"s\"\n";
    toLowerCase += "    (ite (= ch \"T\") \"t\"\n";
    toLowerCase += "    (ite (= ch \"U\") \"u\"\n";
    toLowerCase += "    (ite (= ch \"V\") \"v\"\n";
    toLowerCase += "    (ite (= ch \"W\") \"w\"\n";
    toLowerCase += "    (ite (= ch \"X\") \"x\"\n";
    toLowerCase += "    (ite (= ch \"Y\") \"y\"\n";
    toLowerCase += "    (ite (= ch \"Z\") \"z\"\n";
    toLowerCase += "    ch\n";
    toLowerCase += "    ))))))))))))))))))))))))))\n";
    toLowerCase += ")\n";
    toLowerCase += "(define-fun tolower_match_at ((u String) (l String) (i Int)) Bool\n";
    toLowerCase += "    (=\n";
    toLowerCase += "        (char_tolower (str.at u i))\n";
    toLowerCase += "        (str.at l i)\n";
    toLowerCase += "    )\n";
    toLowerCase += ")\n";
    toLowerCase += "(define-fun str_tolowercase_bounded ((u String) (l String)) Bool\n";
    toLowerCase += "    (and\n";
    toLowerCase += "        (= (str.len u) (str.len l))\n";
    toLowerCase += "        \n";
    for (int i = 0; i < bound; i++) {
        toLowerCase += QString("        (ite (> (str.len u) %1)\n").arg(i);
        toLowerCase += QString("            (tolower_match_at u l %1)\n").arg(i);
        toLowerCase += "            true\n";
        toLowerCase += "        )\n";
    }
    toLowerCase += "    )\n";
    toLowerCase += ")\n\n";

    mPreambleDefinitions.append(toLowerCase);
}

void CVC4ConstraintWriter::preambleAddToUpperCase()
{
    if (mSawToUpperCase) {
        return;
    }
    mSawToUpperCase = true;

    int bound = 5;

    QString toUpperCase;
    toUpperCase += "(define-fun char_toupper ((ch String)) String\n";
    toUpperCase += "    (ite (= ch \"a\") \"A\"\n";
    toUpperCase += "    (ite (= ch \"b\") \"B\"\n";
    toUpperCase += "    (ite (= ch \"c\") \"C\"\n";
    toUpperCase += "    (ite (= ch \"d\") \"D\"\n";
    toUpperCase += "    (ite (= ch \"e\") \"E\"\n";
    toUpperCase += "    (ite (= ch \"f\") \"F\"\n";
    toUpperCase += "    (ite (= ch \"g\") \"G\"\n";
    toUpperCase += "    (ite (= ch \"h\") \"H\"\n";
    toUpperCase += "    (ite (= ch \"i\") \"I\"\n";
    toUpperCase += "    (ite (= ch \"j\") \"J\"\n";
    toUpperCase += "    (ite (= ch \"k\") \"K\"\n";
    toUpperCase += "    (ite (= ch \"l\") \"L\"\n";
    toUpperCase += "    (ite (= ch \"m\") \"M\"\n";
    toUpperCase += "    (ite (= ch \"n\") \"N\"\n";
    toUpperCase += "    (ite (= ch \"o\") \"O\"\n";
    toUpperCase += "    (ite (= ch \"p\") \"P\"\n";
    toUpperCase += "    (ite (= ch \"q\") \"Q\"\n";
    toUpperCase += "    (ite (= ch \"r\") \"R\"\n";
    toUpperCase += "    (ite (= ch \"s\") \"S\"\n";
    toUpperCase += "    (ite (= ch \"t\") \"T\"\n";
    toUpperCase += "    (ite (= ch \"u\") \"U\"\n";
    toUpperCase += "    (ite (= ch \"v\") \"V\"\n";
    toUpperCase += "    (ite (= ch \"w\") \"W\"\n";
    toUpperCase += "    (ite (= ch \"x\") \"X\"\n";
    toUpperCase += "    (ite (= ch \"y\") \"Y\"\n";
    toUpperCase += "    (ite (= ch \"z\") \"Z\"\n";
    toUpperCase += "    ch\n";
    toUpperCase += "    ))))))))))))))))))))))))))\n";
    toUpperCase += ")\n";
    toUpperCase += "(define-fun toupper_match_at ((u String) (l String) (i Int)) Bool\n";
    toUpperCase += "    (=\n";
    toUpperCase += "        (char_toupper (str.at u i))\n";
    toUpperCase += "        (str.at l i)\n";
    toUpperCase += "    )\n";
    toUpperCase += ")\n";
    toUpperCase += "(define-fun str_touppercase_bounded ((u String) (l String)) Bool\n";
    toUpperCase += "    (and\n";
    toUpperCase += "        (= (str.len u) (str.len l))\n";
    toUpperCase += "        \n";
    for (int i = 0; i < bound; i++) {
        toUpperCase += QString("        (ite (> (str.len u) %1)\n").arg(i);
        toUpperCase += QString("            (toupper_match_at u l %1)\n").arg(i);
        toUpperCase += "            true\n";
        toUpperCase += "        )\n";
    }
    toUpperCase += "    )\n";
    toUpperCase += ")\n\n";

    mPreambleDefinitions.append(toUpperCase);
}

void CVC4ConstraintWriter::coercetype(Symbolic::Type from, Symbolic::Type to, std::string expression)
{
    if (from == Symbolic::STRING && to == Symbolic::INT) {

        mExpressionBuffer = "(str.to.int " + expression + ")";
        mExpressionType = Symbolic::INT;
        return;
    }

    if (from == Symbolic::INT && to == Symbolic::STRING) {

        mExpressionBuffer = "(int.to.str " + expression + ")";
        mExpressionType = Symbolic::STRING;
        return;
    }

    SMTConstraintWriter::coercetype(from, to, expression);
}

void CVC4ConstraintWriter::emitDOMConstraints()
{

    std::set<Symbolic::SymbolicObject*>::iterator iter;
    for (iter = mVisitedSymbolicObjects.begin(); iter != mVisitedSymbolicObjects.end(); ++iter) {

        std::string identifier = (*iter)->getSource().getIdentifier();

        // Look up this symbolic object in the list of snapshots and output a snapshot constraint if one is found.

        // TODO: remove
        //qDebug() << QString::fromStdString(identifier); // Includes SYM_IN_ prefix.
        //qDebug() << *(mDomSnapshots.data());

        // If this test fails there will likely be a failed assertion while trying to read back the solver results, as the expected "result" variable will not be present.
        if (mDomSnapshots->contains(identifier)) {

            WebCore::DOMSnapshot* domSnapshot = mDomSnapshots->get(identifier);

            recordAndEmitType(identifier + "_SOLUTIONXPATH", Symbolic::STRING);

            mOutput << std::endl;
            mOutput << "; CONSTRAINTS FOR DOM NODE " << identifier << std::endl;
            mOutput << "(assert (or " << std::endl;

            std::map<WebCore::DOMSnapshotNodeId, WebCore::DOMSnapshotNode*> nodes = domSnapshot->getNodes();
            std::map<WebCore::DOMSnapshotNodeId, WebCore::DOMSnapshotNode*>::iterator iter2;
            for (iter2 = nodes.begin(); iter2 != nodes.end(); ++iter2) {
                WebCore::DOMSnapshotNodeId id = iter2->first;
                WebCore::DOMSnapshotNode* node = iter2->second;

                // symbolic symbolic DOM must resolve to the concrete DOM id
                mOutput << "    (and (= " << encodeIdentifier(identifier) << " " << id << ")";

                // special, emit the xpath to the result object. This is used later as the final result
                mOutput << std::endl << "         (= " \
                        << encodeIdentifier(identifier + "_SOLUTIONXPATH") \
                        << " \"" << CVC4RegexCompiler::escape(node->getXpath()) << "\")";

                // all attributes must match
                WebCore::DOMSnapshotNodeAttributes attributes = node->getAttributes();
                std::set<std::string>::iterator iter3;
                for (iter3 = mUsedSymbolicObjectProperties[(*iter)].begin(); iter3 != mUsedSymbolicObjectProperties[(*iter)].end(); ++iter3) {

                    WebCore::DOMSnapshotNodeAttributes::iterator result = attributes.find((*iter3));
                    std::string value = (result == attributes.end()) ? "" : result->second;

                    mOutput << std::endl << "         (= " \
                            << encodeIdentifier(identifier + "__" + (*iter3)) \
                            << " \"" << CVC4RegexCompiler::escape(value) << "\")";
                }

                mOutput << ")" << std::endl; // and END
            }

            mOutput << "))" << std::endl;
            mOutput << std::endl;

        }
    }

}


}
