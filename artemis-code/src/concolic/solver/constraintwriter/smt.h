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

#ifndef SMT_H
#define SMT_H

#include <fstream>
#include <map>

#include <QSharedPointer>

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"
#include "runtime/input/forms/formfieldrestrictedvalues.h"
#include "concolic/benchmerking.h"

#include "abstract.h"

namespace artemis
{

typedef struct CoercionPromise_t {

    bool isCoerced;
    Symbolic::Type coerceTo;

    CoercionPromise_t(Symbolic::Type coerceTo)
        : isCoerced(false)
        , coerceTo(coerceTo)
    {
    }

} CoercionPromise;

/**
 * Visitor generating symbolic constraints for the
 * SMT solver Z3[1] with the Z3-str extension[2].
 *
 * The emitted syntax is SMT-LIB 2.0
 *
 * If write() returns false then the constraints can
 * not be solved by CVC4. In this case the content
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
class SMTConstraintWriter : public ConstraintWriter, public Symbolic::Visitor
{
public:

    SMTConstraintWriter(ConcolicBenchmarkFeatures disabledFeatures);

    virtual bool write(PathConditionPtr pathCondition, FormRestrictions formRestrictions, std::string outputFile);

    std::string getErrorReason() {
        return mErrorReason;
    }

    int getErrorClause() {
        return mErrorClause;
    }

    static std::string encodeIdentifier(const std::string&);
    static std::string decodeIdentifier(const std::string&);

protected:

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

    // Internal
    virtual void visit(Symbolic::StringRegexSubmatchArray* exp, void* arg);

    // Returns integer values to mExpressionBuffer
    virtual void visit(Symbolic::SymbolicInteger* symbolicinteger, void* args);
    virtual void visit(Symbolic::ConstantInteger* constantinteger, void* args);
    virtual void visit(Symbolic::IntegerBinaryOperation* integerbinaryoperation, void* args);
    virtual void visit(Symbolic::IntegerCoercion* integercoercion, void* args);
    virtual void visit(Symbolic::StringLength* stringlength, void* args);
    virtual void visit(Symbolic::StringRegexSubmatchIndex* submatchIndex, void* arg);
    virtual void visit(Symbolic::IntegerMaxMin* obj, void* arg);

    // Returns string values to mExpressionBuffer
    virtual void visit(Symbolic::SymbolicString* symbolicstring, void* args);
    virtual void visit(Symbolic::ConstantString* constantstring, void* args);
    virtual void visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args);
    virtual void visit(Symbolic::StringCoercion* stringcoercion, void* args);
    virtual void visit(Symbolic::StringCharAt* stringcharat, void* arg);
    virtual void visit(Symbolic::StringRegexReplace* stringregexreplace, void* args);
    virtual void visit(Symbolic::StringReplace* stringreplace, void* args);
    virtual void visit(Symbolic::StringRegexSubmatchArrayAt* exp, void* arg);

    // Returns boolean values to mExpressionBuffer
    virtual void visit(Symbolic::SymbolicBoolean* symbolicboolean, void* args);
    virtual void visit(Symbolic::ConstantBoolean* constantboolean, void* args);
    virtual void visit(Symbolic::BooleanCoercion* booleancoercion, void* args);
    virtual void visit(Symbolic::BooleanBinaryOperation* booleanbinaryoperation, void* args);
    virtual void visit(Symbolic::StringRegexSubmatch* submatch, void* arg);

    // Returns Object values to mExpressionBuffer
    virtual void visit(Symbolic::StringRegexSubmatchArrayMatch* exp, void* arg);
    virtual void visit(Symbolic::ConstantObject* obj, void* arg);
    virtual void visit(Symbolic::ObjectBinaryOperation* obj, void* arg);

    // Output writing
    virtual void preVisitPathConditionsHook(QSet<QString> varsUsed);
    virtual void postVisitPathConditionsHook();

    virtual std::string ifLabel();

    /**
     * SMT does not support mixing constraints on strings,
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
    void recordAndEmitType(const std::string&, Symbolic::Type type);
    bool checkType(Symbolic::Type expected);

    virtual void coercetype(Symbolic::Type from, Symbolic::Type to, std::string expression);

    std::string emitAndReturnNewTemporary(Symbolic::Type type);
    void emitConst(const std::string& identifier, Symbolic::Type type);

    static inline std::string stringfindreplace(const std::string& string, const std::string& search, const std::string& replace);

    void error(std::string reason);

    std::map<std::string, Symbolic::Type> mTypemap;
    std::ofstream mOutput;

    // holds the current subexpression returned by the previous call to visit
    std::string mExpressionBuffer;

    // indicates the current type of the subexpression returned in mExpressionBuffer
    Symbolic::Type mExpressionType;

    bool mError; // indicates that an error occured when writing the file
    std::string mErrorReason;

    // If an error occured which was caused by a particular clause in the PC its index is recorded. Otherwise mErrorClause is -1.
    int mCurrentClause;
    int mErrorClause;

    unsigned int mNextTemporarySequence;

    FormRestrictions mFormRestrictions;

    // Benchmarking
    ConcolicBenchmarkFeatures mDisabledFeatures;
};

typedef QSharedPointer<SMTConstraintWriter> SMTConstraintWriterPtr;

}

#endif // Z3STR_H
