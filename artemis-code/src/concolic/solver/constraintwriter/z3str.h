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
 *
 * TODO: A better approach to determining the types and
 *   coercions required. Currently we apply coercions
 *   as the appear in the PC. It may be more powerful
 *   (or clearer) to first pre-process the PC to examine
 *   which variables are used in which contects. Then
 *   it should be possible to determine the best choice
 *   of type for each input variable and which coercions
 *   are required.
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
     * and ``mExpressionType``. New symbols are written directly to ``mOutput``.
     *
     * The type of the expression written to mExpressionBuffer should match the
     * type stored in mExpressionType.
     *
     * Each call to visit should
     * 1. Check the types (returned via mExpressionType) of any recursive calls
     *      to the visitors match those required.
     * 2. Write the subexpression created by the call to mExpressionBuffer.
     * 3. Write the type of the subexpression to mExpressionType
     *
     * Symbolic values are bound to the relevant type according to the coercions
     * in the PC. We ignore coercions from inputs to integers (which the solver
     * cannot handle but we can use) and a coercion from a non-input string
     * expression to an integer is not supported.
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
    void visit(Symbolic::StringLength* stringlength);

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
     * We treat all input variables as either strings or ints,
     * and support certin types of mixing constraints on the
     * same variable via coercions.
     *
     * E.g. a string input can be coerced into an bool, and
     * we can apply as many boolean constraints to it as we
     * want. We can also support string constraints on the
     * same variable.
     *
     * Integer constraints are handled slightly differently
     * as we cannot support general coercions from strings
     * to ints. However, we allow (string) input variables to
     * be coerced to integers silently and solve these
     * constraints as integers.
     *
     * Mixing the type of a given input is always an error.
     *
     * We also support direct mixing of the string and int
     * domains via integer constraints on string length.
     */

    void recordAndEmitType(const Symbolic::SymbolicSource&, Symbolic::Type type);
    inline bool checkType(Symbolic::Type expected);

    void coercetype(Symbolic::Type from, Symbolic::Type to, std::string expression);

    static inline std::string stringfindreplace(const std::string& string, const std::string& search, const std::string& replace);

    void error(std::string reason);

    std::map<std::string, Symbolic::Type> mTypemap;
    std::ofstream mOutput;
    std::ofstream mConstriantLog;

    // holds the current subexpression returned by the previous call to visit
    std::string mExpressionBuffer;

    // indicates the current type of the subexpression returned in mExpressionBuffer
    Symbolic::Type mExpressionType;

    bool mError; // indicates that an error occured when writing the file
    std::string mErrorReason;
};

typedef QSharedPointer<Z3STRConstraintWriter> Z3STRConstraintWriterPtr;

}

#endif // Z3STR_H
