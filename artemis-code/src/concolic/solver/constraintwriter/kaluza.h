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

#ifndef KALUZA_H
#define KALUZA_H

#include <fstream>
#include <map>

#include <QSharedPointer>

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"

#include "abstract.h"

#ifdef ARTEMIS

namespace artemis
{

/**
 * Visitor generating symbolic constraints for the
 * SMT solver Kaluza[1].
 *
 * If write() returns false then the constraints can
 * not be solved by Kaluza. In this case the content
 * of the constraint file is undefined and the result
 * should be interpreted as UNSAT.
 *
 * [1] http://webblaze.cs.berkeley.edu/2010/kaluza/
 */
class KaluzaConstraintWriter : public ConstraintWriter, public Symbolic::Visitor
{
public:

    KaluzaConstraintWriter();

    bool write(PathConditionPtr pathCondition, std::string outputFile);

private:

    void visit(Symbolic::SymbolicInteger* symbolicinteger, void* args);
    void visit(Symbolic::ConstantInteger* constantinteger, void* args);
    void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* args);
    void visit(Symbolic::IntegerCoercion* integercoercion, void* args);
    void visit(Symbolic::SymbolicString* symbolicstring, void* args);
    void visit(Symbolic::ConstantString* constantstring, void* args);
    void visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args);
    void visit(Symbolic::StringCoercion* stringcoercion, void* args);
    void visit(Symbolic::StringCharAt* stringcharat, void* arg);
    void visit(Symbolic::StringRegexReplace* stringregexreplace, void* args);
    void visit(Symbolic::StringReplace* stringreplace, void* args);
    void visit(Symbolic::SymbolicBoolean* symbolicboolean, void* args);
    void visit(Symbolic::ConstantBoolean* constantboolean, void* args);
    void visit(Symbolic::BooleanCoercion* booleancoercion, void* args);
    void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* args);
    void visit(Symbolic::StringLength* stringlength, void* args);

    /**
     * Kaluza does not support mixing constraints on strings,
     * bools and integers. Thus, we allow type coercions but
     * we only support one type of constraint to be applied
     * to any symbol.
     *
     * E.g. an input string can be coerced into an int, and
     * we can apply as many integer constraints to it as we
     * want.
     */
    void recordType(const std::string& identifer, Symbolic::Type type);

    std::map<std::string, Symbolic::Type> mTypemap;
    std::ofstream mOutput;
    std::string mIdentifierStore;
    unsigned int mNextTemporaryIdentifier;

    bool mError; // indicates that an error occured when writing the file
    std::string mErrorReason;
};

typedef QSharedPointer<KaluzaConstraintWriter> KaluzaConstraintWriterPtr;

}

#endif
#endif // KALUZA_H
