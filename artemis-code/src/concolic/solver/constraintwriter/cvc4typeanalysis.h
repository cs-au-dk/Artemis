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

#ifndef CVC4TYPEANALYSIS_H
#define CVC4TYPEANALYSIS_H

#include <QSharedPointer>

#include <map>
#include <string>

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"

namespace artemis
{

class CVC4TypeAnalysis : public Symbolic::Visitor
{
public:

    CVC4TypeAnalysis();
    virtual ~CVC4TypeAnalysis() {}

    void analyze(Symbolic::Expression* expr);
    void reset();

    enum CVC4Type {
        STRING = 1,
        INTEGER = 2,
        BOOLEAN = 4,
        OBJECT = 8,
        WEAK_INTEGER = 16,
        WEAK_STRING = 32,
        WEAK_BOOLEAN = 64,
        WEAK_OBJECT = 128
    };

    bool hasUniqueConstraint(const std::string&, CVC4Type);

protected:

    void visit(Symbolic::SymbolicInteger* symbolicinteger, void* arg);
    void visit(Symbolic::ConstantInteger* constantinteger, void* arg);
    void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* arg);
    void visit(Symbolic::IntegerCoercion* integercoercion, void* arg);
    void visit(Symbolic::IntegerMaxMin* integermaxmin, void* arg);
    void visit(Symbolic::ConstantObject* constantobject, void* arg);
    void visit(Symbolic::ObjectBinaryOperation* objectbinaryoperation, void* arg);
    void visit(Symbolic::SymbolicString* symbolicstring, void* arg);
    void visit(Symbolic::ConstantString* constantstring, void* arg);
    void visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* arg);
    void visit(Symbolic::StringCoercion* stringcoercion, void* arg);
    void visit(Symbolic::StringLength* stringlength, void* arg);
    void visit(Symbolic::StringReplace* stringreplace, void* arg);
    void visit(Symbolic::StringCharAt* stringcharat, void* arg);
    void visit(Symbolic::StringRegexReplace* stringregexreplace, void* arg);
    void visit(Symbolic::StringRegexSubmatch* stringregexsubmatch, void* arg);
    void visit(Symbolic::StringRegexSubmatchIndex* stringregexsubmatchindex, void* arg);
    void visit(Symbolic::StringRegexSubmatchArray* stringregexsubmatcharray, void* arg);
    void visit(Symbolic::StringRegexSubmatchArrayAt* stringregexsubmatcharrayat, void* arg);
    void visit(Symbolic::StringRegexSubmatchArrayMatch* stringregexsubmatcharraymatch, void* arg);
    void visit(Symbolic::SymbolicBoolean* symbolicboolean, void* arg);
    void visit(Symbolic::ConstantBoolean* constantboolean, void* arg);
    void visit(Symbolic::BooleanCoercion* booleancoercion, void* arg);
    void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* arg);
    void visit(Symbolic::StringIndexOf* stringindexof, void* arg);
    void visit(Symbolic::SymbolicObject* symbolicobject, void* arg);
    void visit(Symbolic::ObjectArrayIndexOf* objectarrayindexof, void* arg);
    void visit(Symbolic::SymbolicObjectPropertyString* obj, void* arg);

    void recordConstraint(const std::string&, CVC4Type);

    std::map<std::string, int> mType;

    // indicates the current type of the subexpression returned in mExpressionBuffer
    CVC4Type mExpressionType;
};

typedef QSharedPointer<CVC4TypeAnalysis> CVC4TypeAnalysisPtr;

}

#endif // CVC4TYPEANALYSIS_H
