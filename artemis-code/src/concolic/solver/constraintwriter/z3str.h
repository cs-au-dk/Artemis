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

#ifndef Z3STR_H
#define Z3STR_H

#include <fstream>
#include <map>

#include <QSharedPointer>

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"

#include "abstract.h"

namespace artemis
{

/**
 * Visitor generating symbolic constraints for the
 * SMT solver Z3[1] with the Z3-str extension[2].
 *
 * The emitted syntax is SMT-LIB 2.0
 *
 * If write() returns false then the constraints can
 * not be solved by Z3-str. In this case the content
 * of the constraint file is undefined and the result
 * should be interpreted as UNSAT.
 *
 * [1] http://z3.codeplex.com/
 * [2] http://www.cs.purdue.edu/homes/zheng16/str/
 */
class Z3STRConstraintWriter : public ConstraintWriter, public Symbolic::Visitor
{
public:

    Z3STRConstraintWriter();

    bool write(PathConditionPtr pathCondition, std::string outputFile);

    static std::string encodeIdentifier(const std::string&);
    static std::string decodeIdentifier(const std::string&);

private:

    /**
     * Invariants between each call to visit:
     * --------------------------------------
     *
     * Each call to visit writes (returns) its value into ``mExpressionBuffer``
     * and new symbols are written directly to ``mOutput``.
     *
     * The type of the expression written to mExpressionBuffer should match the
     * expected type by the call to visit. This type is stored in mExpressionType.
     *
     * Each call to visit should
     * 1. Check if its own type (documented below) matches mExpressionType, if not
     *    it should mark the translation as an error.
     * 2. Write the subexpression created by the call to mExpressionBuffer.
     *    ! This subexpression should be of type mExpressionType
     *
     * Symbolic values are bound to the relevant type (according to mExpressionType)
     * the first time they are accessed (responsibility of the symbolic* visitors).
     *
     * Constant values are automatically converted to the relevant type (according to
     * mExpressionType) when accessed (responsibility of the constant* visitors).
     *
     */

    // Returns integer values to mExpressionBuffer
    void visit(Symbolic::SymbolicInteger* symbolicinteger);
    void visit(Symbolic::ConstantInteger* constantinteger);
    void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation);
    void visit(Symbolic::IntegerCoercion* integercoercion);

    // Returns string values to mExpressionBuffer
    void visit(Symbolic::SymbolicString* symbolicstring);
    void visit(Symbolic::ConstantString* constantstring);
    void visit(Symbolic::StringBinaryOperation* stringbinaryoperation);
    void visit(Symbolic::StringCoercion* stringcoercion);
    void visit(Symbolic::StringRegexReplace* stringregexreplace);
    void visit(Symbolic::StringReplace* stringreplace);

    // Returns boolean values to mExpressionBuffer
    void visit(Symbolic::SymbolicBoolean* symbolicboolean);
    void visit(Symbolic::ConstantBoolean* constantboolean);
    void visit(Symbolic::BooleanCoercion* booleancoercion);
    void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation);

    /**
     * Z3-str does not support mixing constraints on strings,
     * bools and integers. Thus, we allow type coercions but
     * we only support one type of constraint to be applied
     * to any symbol.
     *
     * E.g. a string input can be coerced into an int, and
     * we can apply as many integer constraints to it as we
     * want. However, if that is the case then we will not
     * allow any string constraints on said string.
     *
     * In other words, we don't support constraints mixing
     * the different domains (int, real, bool, string)
     * with the exception of integer constraints on string
     * lengths.
     *
     * We do this by recording the "type" an input is expected
     * to be when used, regardless of how it has been coerced.
     * That is, we ignore all coercions and apply the type in a
     * lazy manner as needed. We register a type error if the
     * same input is given two conflicting types.
     *
     * This is similar to the Kaluza behaviour.
     */
    void recordAndEmitType(const Symbolic::SymbolicSource&, Symbolic::Type type);
    inline bool checkType(Symbolic::Type expected);

    void coercetype(Symbolic::Type from, Symbolic::Type to, std::string expression);

    static inline std::string stringfindreplace(const std::string& string, const std::string& search, const std::string& replace);

    std::map<std::string, Symbolic::Type> mTypemap;
    std::ofstream mOutput;

    // holds the current subexpression returned by the previous call to visit
    std::string mExpressionBuffer;

    // indicates the current type of the subexpression, used for determening
    // the correct type of symbolic values
    Symbolic::Type mExpressionType;

    bool mError; // indicates that an error occured when writing the file
    std::string mErrorReason;
};

}

#endif // Z3STR_H
