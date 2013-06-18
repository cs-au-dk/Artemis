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

#include <tr1/unordered_set>
#include <inttypes.h>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"
#include "JavaScriptCore/instrumentation/bytecodeinfo.h"
#include "JavaScriptCore/runtime/JSString.h"

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitors/printer.h"

#include "symbolicinterpreter.h"
#include <QDebug>

#ifdef ARTEMIS


namespace Symbolic
{

unsigned int NEXT_SYMBOLIC_ID = 0;

const char* opToString(OP op) {
    static const char* OPStrings[] = {
        "==", "!=", "===", "!==", "<=", "<", ">=", ">",
        "+", "-", "*", "/", "%"
    };

    return OPStrings[op];
}

SymbolicInterpreter::SymbolicInterpreter() :
    m_pc(NULL),
    m_nextSymbolicValue(0),
    m_inSession(false),
    m_shouldGC(false)
{
}

void SymbolicInterpreter::ail_call(JSC::CallFrame*, const JSC::Instruction*, JSC::BytecodeInfo&)
{
}

void SymbolicInterpreter::ail_call_native(JSC::CallFrame* callFrame,
                                          const JSC::Instruction*,
                                          JSC::BytecodeInfo&,
                                          JSC::native_function_ID_t functionID)
{

    if (!m_inSession) return;

    const NativeFunction* nativeFunction = m_nativeFunctions.find(functionID);

    if (nativeFunction == NULL) {
        //std::cout << "AIL_CALL_NATIVE <Unknown native function>" << std::endl;
        return;
    }

    //std::cout << "AIL_CALL_NATIVE <" << nativeFunction->getName() << ">" << std::endl;
}




JSC::JSValue SymbolicInterpreter::ail_op_binary(JSC::CallFrame* callFrame,
                                                const JSC::Instruction*,
                                                JSC::BytecodeInfo& info,
                                                JSC::JSValue& x,
                                                OP op,
                                                JSC::JSValue& y,
                                                JSC::JSValue result)
{

    if (!m_inSession) return result;

    if (!x.isSymbolic() && !y.isSymbolic()) {
        return result; // not symbolic
    }

    info.setSymbolic();

    bool neq = false;
    IntegerBinaryOp intOp = INT_MODULO;
    StringBinaryOp strOp = STRING_GT;
    switch (op) {

    case NOT_EQUAL:
        neq = true;
    case EQUAL: {
        JSC::JSValue xx = x.toPrimitive(callFrame);
        JSC::JSValue yy = y.toPrimitive(callFrame);

        // Case 1: Number
        if (xx.isNumber() && yy.isNumber()) {

            Symbolic::IntegerExpression* sx = x.generateIntegerExpression(callFrame);
            Symbolic::IntegerExpression* sy = y.generateIntegerExpression(callFrame);

            result.makeSymbolic(new IntegerBinaryOperation(sx, neq?INT_NEQ:INT_EQ, sy));

            ASSERT(result.isSymbolic());

            return result;

        }


        // Case 2: String
        if (xx.isString() && yy.isString()) {
            Symbolic::StringExpression* sx = x.generateStringExpression(callFrame);
            Symbolic::StringExpression* sy = y.generateStringExpression(callFrame);

            result.makeSymbolic(new StringBinaryOperation(sx, neq?STRING_NEQ:STRING_EQ, sy));

            ASSERT(result.isSymbolic());

            return result;
        }

        // Case 3: Object nullness
        if (x.isUndefinedOrNull()) {
            return result;
        }

        if (y.isUndefinedOrNull()) {
            return result;
        }

        // Case 4: Object identity
        if (x.isObject() || y.isObject()) {
            return result;
        }


        // Case 5: Basecase, (pure boolean?)
        if(xx.isBoolean() && yy.isBoolean()){
            Symbolic::BooleanExpression* sx = x.generateBooleanExpression(callFrame);
            Symbolic::BooleanExpression* sy = y.generateBooleanExpression(callFrame);
            result.makeSymbolic(new BooleanBinaryOperation(sx,neq?BOOL_NEQ:BOOL_EQ,sy));
            return result;
        }

        // Case 6: Mixed string/boolean and <other>
        if (xx.isString() || yy.isString() || xx.isBoolean() || yy.isBoolean()) {

            Symbolic::IntegerExpression* sx = NULL;
            Symbolic::IntegerExpression* sy = NULL;

            sx = x.isNumber()? x.generateIntegerExpression(callFrame):x.generateIntegerCoercionExpression(callFrame);
            sy = y.isNumber()? y.generateIntegerExpression(callFrame):y.generateIntegerCoercionExpression(callFrame);

            ASSERT(sx != NULL);
            ASSERT(sy != NULL);

            result.makeSymbolic(new IntegerBinaryOperation(sx, neq?INT_NEQ:INT_EQ, sy));

            ASSERT(result.isSymbolic());

            return result;
        }

        return result;

        break;

    }


    case NOT_STRICT_EQUAL:
        neq = true;
    case STRICT_EQUAL:
        if(x.isString() && y.isString()){
            Symbolic::StringExpression* sx = x.generateStringExpression(callFrame);
            Symbolic::StringExpression* sy = y.generateStringExpression(callFrame);
            result.makeSymbolic(new StringBinaryOperation(sx,neq?STRING_SNEQ:STRING_SEQ,sy));
            return result;
        }

        if(x.isNumber() && y.isNumber()){
            Symbolic::IntegerExpression* sx = x.generateIntegerExpression(callFrame);
            Symbolic::IntegerExpression* sy = y.generateIntegerExpression(callFrame);
            result.makeSymbolic(new IntegerBinaryOperation(sx,neq?INT_SNEQ:INT_SEQ,sy));
            return result;
        }

        if(x.isBoolean() && y.isBoolean()){
            Symbolic::BooleanExpression* sx = x.generateBooleanExpression(callFrame);
            Symbolic::BooleanExpression* sy = y.generateBooleanExpression(callFrame);
            result.makeSymbolic(new BooleanBinaryOperation(sx,neq?BOOL_SNEQ:BOOL_SEQ,sy));
            return result;
        }


        break;
    case LESS_EQ:{
        intOp = INT_LEQ;
        strOp = STRING_LEQ;
    }
    case LESS_STRICT:
        if(intOp == INT_MODULO){
            intOp = INT_LT;
            strOp = STRING_LT;
        }
    case GREATER_EQ:
        if(intOp == INT_MODULO){
            intOp = INT_GEQ;
            strOp = STRING_GEQ;
        }
    case GREATER_STRICT:{
        if(intOp == INT_MODULO){
            intOp = INT_GT;
        }
        JSC::JSValue xx = x.toPrimitive(callFrame);
        JSC::JSValue yy = y.toPrimitive(callFrame);
        if(xx.isString() && yy.isString()){
            Symbolic::StringExpression* sx = x.generateStringExpression(callFrame);
            Symbolic::StringExpression* sy = y.generateStringExpression(callFrame);
            result.makeSymbolic(new StringBinaryOperation(sx,strOp,sy));
            return result;
        }
        Symbolic::IntegerExpression* sx = xx.isNumber()?x.generateIntegerExpression(callFrame):x.generateIntegerCoercionExpression(callFrame);
        Symbolic::IntegerExpression* sy = yy.isNumber()?y.generateIntegerExpression(callFrame):y.generateIntegerCoercionExpression(callFrame);
        result.makeSymbolic(new IntegerBinaryOperation(sx,intOp,sy));
        return result;
        break;
}


    case ADD: {

        // case 1: number
        if (x.isNumber() && y.isNumber()) {

            Symbolic::IntegerExpression* sx = x.generateIntegerExpression(callFrame);
            Symbolic::IntegerExpression* sy = y.generateIntegerExpression(callFrame);

            ASSERT(sx);
            ASSERT(sy);

            result.makeSymbolic(new IntegerBinaryOperation(sx, INT_ADD, sy));

            ASSERT(result.isSymbolic());

            return result;
        }
        JSC::JSValue xx = x.toPrimitive(callFrame);
        JSC::JSValue yy = y.toPrimitive(callFrame);

        // case 2: string
        if (xx.isString()) {

            Symbolic::StringExpression* sx = NULL;
            Symbolic::StringExpression* sy = NULL;

            sx = x.generateStringExpression(callFrame);

            if (yy.isString()) {
                sy = y.generateStringExpression(callFrame);
            } else {
                // y string coercion
                sy = y.generateStringCoercionExpression(callFrame);
            }

            ASSERT(sx != NULL);
            ASSERT(sy != NULL);

            result.makeSymbolic(new StringBinaryOperation(sx, CONCAT, sy));

            ASSERT(result.isSymbolic());

            return result;
        }

        if (yy.isString()) {
            // xx string coercion

            Symbolic::StringExpression* sx = NULL;
            Symbolic::StringExpression* sy = NULL;

            sx = x.generateStringCoercionExpression(callFrame);
            sy = y.generateStringExpression(callFrame);

            ASSERT(sx != NULL);
            ASSERT(sy != NULL);

            result.makeSymbolic(new StringBinaryOperation(sx, CONCAT, sy));

            ASSERT(result.isSymbolic());

            return result;
        }

        // case 4: primitive number coercion

        Symbolic::IntegerExpression* sx = NULL;
        Symbolic::IntegerExpression* sy = NULL;

        sx = xx.isNumber()? x.generateIntegerExpression(callFrame):x.generateIntegerCoercionExpression(callFrame);
        sy = yy.isNumber()? y.generateIntegerExpression(callFrame):y.generateIntegerCoercionExpression(callFrame);

        ASSERT(sx != NULL);
        ASSERT(sy != NULL);

        result.makeSymbolic(new IntegerBinaryOperation(sx, INT_ADD, sy));

        ASSERT(result.isSymbolic());

        return result;
    }

    case SUBTRACT:
        intOp = INT_SUBTRACT;
    case MULTIPLY:
        intOp = intOp == INT_MODULO?INT_MULTIPLY:intOp;
    case DIVIDE:
        intOp = intOp == INT_MODULO?INT_DIVIDE:intOp;
    case MODULO: {
        Symbolic::IntegerExpression* sx = NULL;
        Symbolic::IntegerExpression* sy = NULL;
        sx = x.toPrimitive(callFrame).isNumber()?x.generateIntegerExpression(callFrame):x.generateIntegerCoercionExpression(callFrame);
        sy = y.toPrimitive(callFrame).isNumber()?y.generateIntegerExpression(callFrame):y.generateIntegerCoercionExpression(callFrame);

        ASSERT(sx != NULL);
        ASSERT(sy != NULL);

        result.makeSymbolic(new IntegerBinaryOperation(sx,intOp,sy));
        ASSERT(result.isSymbolic());
        return result;

        break;
    }
    }

    //std::string xValue = x.isSymbolic() ? x.asSymbolic()->value : std::string(x.toString(callFrame).ascii().data());
    //std::string yValue = y.isSymbolic() ? y.asSymbolic()->value : std::string(y.toString(callFrame).ascii().data());

    //std::string value = std::string("(") + xValue + std::string(opToString(op)) + yValue + std::string(")");

    //std::cout << "AIL_OP_BINARY " << value << std::endl;

    return result;
}

void SymbolicInterpreter::ail_jmp_iff(JSC::CallFrame* callFrame,
                                      const JSC::Instruction* vPC,
                                      JSC::BytecodeInfo& info,
                                      JSC::JSValue& condition,
                                      bool jumps)
{

    // Notify Artemis directly about this branch.
    // TODO: what to send?
    // TODO: should this be after the m_inSession guard?
    jscinst::get_jsc_listener()->javascript_branch_executed(condition.toString(callFrame).ascii().data(), jumps, condition.isSymbolic());

    if (!m_inSession) return;

    if (condition.isSymbolic()) {
        info.setSymbolic();
        m_pc->append(condition.asSymbolic(), jumps);
    }
}

void SymbolicInterpreter::fatalError(JSC::CodeBlock* codeBlock, std::string reason)
{
    std::cerr << reason << std::endl;
    exit(1);
}

void SymbolicInterpreter::preExecution(JSC::CallFrame* callFrame)
{
    if (m_shouldGC) {
        /*
         * Disable GC, and only GC at the beginning of each session.
         * DomNodes (the JS bindings) are GC'ed, removing any symbolic
         * information stored in them.
         */

        JSC::JSGlobalData* jsGlobalData = &callFrame->globalData();
        JSC::Heap* heap = &jsGlobalData->heap;

        heap->notifyIsSafeToCollect();
        heap->collectAllGarbage();
        heap->notifyIsNotSafeToCollect();

        m_shouldGC = false;
    }
}

void SymbolicInterpreter::beginSession()
{
    m_shouldGC = true;
    m_inSession = true;
    m_pc = new PathCondition();
}

void SymbolicInterpreter::endSession()
{
    m_inSession = false;

    qDebug() << "PC size: " << m_pc->size();

    int i;
    for (i = 0; i < m_pc->size(); i++) {
        Printer printer;
        m_pc->get(i).first->accept(&printer);
        qDebug() << "PC[" << i << "]: " << QString::fromStdString(printer.getResult());
    }
}

PathCondition* SymbolicInterpreter::getPathCondition()
{
    return m_pc;
}

std::string SymbolicInterpreter::generatePathConditionString() {

    std::stringstream sstrm;

    for (int i = 0; i < m_pc->size(); i++) {

        Printer printer;
        m_pc->get(i).first->accept(&printer);

        sstrm << "PC[" << i << "]: " << printer.getResult() << std::endl;
    }

    return sstrm.str();
}


}

#endif
