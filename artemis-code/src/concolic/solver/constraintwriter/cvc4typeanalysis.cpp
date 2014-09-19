/*
 * Copyright 2014 Aarhus University
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

#include "cvc4typeanalysis.h"

#define ENABLE_COERCION_OPTIMIZATION

namespace artemis
{

CVC4TypeAnalysis::CVC4TypeAnalysis()
    : mExpressionType(BOOLEAN)
{

}

void CVC4TypeAnalysis::analyze(Symbolic::Expression* expr) {

    mExpressionType = BOOLEAN;
    expr->accept(this);

}

void CVC4TypeAnalysis::reset() {
    mType.clear();
}

void CVC4TypeAnalysis::recordConstraint(const std::string& identifier, CVC4Type type) {

    std::map<std::string, int>::iterator iter = mType.find(identifier);

    if (iter != mType.end()) {
        iter->second = iter->second | type;
    } else {
        mType.insert(std::pair<std::string, int>(identifier, type));
    }
}

bool CVC4TypeAnalysis::hasUniqueConstraint(const std::string& identifier, CVC4Type type) {

    std::map<std::string, int>::iterator iter = mType.find(identifier);

    assert(iter != mType.end());
    return iter->second == type;
}

void CVC4TypeAnalysis::visit(Symbolic::SymbolicInteger* symbolicinteger, void* arg) {

    recordConstraint(symbolicinteger->getSource().getIdentifier(), mExpressionType);

}

void CVC4TypeAnalysis::visit(Symbolic::ConstantInteger* constantinteger, void* arg) {
    // NO-OP
}

void CVC4TypeAnalysis::visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* arg) {

    mExpressionType = INTEGER;
    integerbinaryoperation->getLhs()->accept(this);

    mExpressionType = INTEGER;
    integerbinaryoperation->getRhs()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::IntegerCoercion* integercoercion, void* arg) {

    mExpressionType = WEAK_INTEGER;
    integercoercion->getExpression()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::IntegerMaxMin* obj, void* arg) {

    std::list<Symbolic::Expression*> expressions = obj->getExpressions();
    std::list<Symbolic::Expression*>::iterator iter;

    for (iter = expressions.begin(); iter != expressions.end(); iter++) {
        mExpressionType = INTEGER;
        Symbolic::Expression* expression = *iter;
        expression->accept(this);
    }

}

void CVC4TypeAnalysis::visit(Symbolic::ConstantObject* constantobject, void* arg) {
    // NO-OP
}

void CVC4TypeAnalysis::visit(Symbolic::ObjectBinaryOperation* objectbinaryoperation, void* arg) {

    mExpressionType = OBJECT;
    objectbinaryoperation->getLhs()->accept(this);

    mExpressionType = OBJECT;
    objectbinaryoperation->getRhs()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::SymbolicString* symbolicstring, void* arg) {

    recordConstraint(symbolicstring->getSource().getIdentifier(), mExpressionType);

}

void CVC4TypeAnalysis::visit(Symbolic::ConstantString* constantstring, void* arg) {
    // NO-OP
}

void CVC4TypeAnalysis::visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* arg) {

    mExpressionType = STRING;
    stringbinaryoperation->getLhs()->accept(this);

    mExpressionType = STRING;
    stringbinaryoperation->getRhs()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringCoercion* stringcoercion, void* arg) {

    mExpressionType = WEAK_STRING;
    stringcoercion->getExpression()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringLength* stringlength, void* arg) {

    mExpressionType = STRING;
    stringlength->getString()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringReplace* stringreplace, void* arg) {

    mExpressionType = STRING;
    stringreplace->getSource()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringCharAt* stringcharat, void* arg) {

    mExpressionType = STRING;
    stringcharat->getSource()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringRegexReplace* obj, void* arg) {

    // special case input filtering (filters matching X and replacing with "")
    if (obj->getReplace()->compare("") == 0) {

        mExpressionType = mExpressionType; // don't apply any strong constraints
        obj->getSource()->accept(this);

    } else {
        mExpressionType = STRING;
        obj->getSource()->accept(this);
    }
}

void CVC4TypeAnalysis::visit(Symbolic::StringRegexSubmatch* stringregexsubmatch, void* arg) {

    mExpressionType = STRING;
    stringregexsubmatch->getSource()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringRegexSubmatchIndex* stringregexsubmatchindex, void* arg) {

    mExpressionType = STRING;
    stringregexsubmatchindex->getSource()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringRegexSubmatchArray* stringregexsubmatcharray, void* arg) {

    mExpressionType = STRING;
    stringregexsubmatcharray->getSource()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringRegexSubmatchArrayAt* obj, void* arg) {
    obj->getMatch()->accept(this);
}

void CVC4TypeAnalysis::visit(Symbolic::StringRegexSubmatchArrayMatch* obj, void* arg) {
    obj->getMatch()->accept(this);
}

void CVC4TypeAnalysis::visit(Symbolic::SymbolicBoolean* symbolicboolean, void* arg) {

    recordConstraint(symbolicboolean->getSource().getIdentifier(), mExpressionType);

}

void CVC4TypeAnalysis::visit(Symbolic::ConstantBoolean* constantboolean, void* arg) {
    // NO-OP
}

void CVC4TypeAnalysis::visit(Symbolic::BooleanCoercion* booleancoercion, void* arg) {

    mExpressionType = WEAK_BOOLEAN;
    booleancoercion->getExpression()->accept(this);


}

void CVC4TypeAnalysis::visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* arg) {

    mExpressionType = BOOLEAN;
    booleanbinaryoperation->getLhs()->accept(this);

    mExpressionType = BOOLEAN;
    booleanbinaryoperation->getRhs()->accept(this);

}

void CVC4TypeAnalysis::visit(Symbolic::StringIndexOf* indexof, void* arg) {

    mExpressionType = STRING;
    indexof->getSource()->accept(this);

    mExpressionType = STRING;
    indexof->getPattern()->accept(this);

    mExpressionType = INTEGER;
    indexof->getOffset()->accept(this);

}

}
