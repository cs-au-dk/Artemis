/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
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

    bool write(PathConditionPtr pathCondition, std::string outputFile);

private:

    KaluzaConstraintWriter();

    void visit(Symbolic::SymbolicInteger* symbolicinteger);
    void visit(Symbolic::ConstantInteger* constantinteger);
    void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation);
    void visit(Symbolic::IntegerCoercion* integercoercion);
    void visit(Symbolic::SymbolicString* symbolicstring);
    void visit(Symbolic::ConstantString* constantstring);
    void visit(Symbolic::StringBinaryOperation* stringbinaryoperation);
    void visit(Symbolic::StringCoercion* stringcoercion);
    void visit(Symbolic::StringRegexReplace* stringregexreplace);
    void visit(Symbolic::StringReplace* stringreplace);
    void visit(Symbolic::SymbolicBoolean* symbolicboolean);
    void visit(Symbolic::ConstantBoolean* constantboolean);
    void visit(Symbolic::BooleanCoercion* booleancoercion);
    void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation);

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

}

#endif
#endif // KALUZA_H
