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

#ifndef CONSTRAINTWRITER_H
#define CONSTRAINTWRITER_H

#include <fstream>
#include <string>

#include "symbolic/expr.h"

#include "symbolic/expression/visitor.h"

#ifdef ARTEMIS

namespace Symbolic
{

class ConstraintWriter : public Visitor
{
public:
    ConstraintWriter(std::string output_filename);

    void visit(SymbolicInteger* symbolicinteger);
    void visit(ConstantInteger* constantinteger);
    void visit(IntegerBinaryOperation* integerbinaryoperation);
    void visit(IntegerCoercion* integercoercion);
    void visit(SymbolicString* symbolicstring);
    void visit(ConstantString* constantstring);
    void visit(StringBinaryOperation* stringbinaryoperation);
    void visit(StringCoercion* stringcoercion);
    void visit(StringRegexReplace* stringregexreplace) __attribute__((noreturn));
    void visit(StringReplace* stringreplace) __attribute__((noreturn));
    void visit(SymbolicBoolean* symbolicboolean);
    void visit(ConstantBoolean* constantboolean);
    void visit(BooleanCoercion* booleancoercion);
    void visit(BooleanBinaryOperation* booleanbinaryoperation);

    void commit();

private:
    std::ofstream mOutput;

    std::string* mIdentifierStore;
    unsigned int mNextTemporaryIdentifier;
};

}

#endif
#endif // CONSTRAINTWRITER_H
