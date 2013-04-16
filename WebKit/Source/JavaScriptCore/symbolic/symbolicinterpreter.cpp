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

#include <iostream>
#include <tr1/unordered_set>
#include <inttypes.h>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"
#include "JavaScriptCore/instrumentation/bytecodeinfo.h"
#include "JavaScriptCore/runtime/JSString.h"

#include "JavaScriptCore/symbolic/expression/integerbinaryoperation.h"
#include "JavaScriptCore/symbolic/expression/symbolicinteger.h"
#include "JavaScriptCore/symbolic/expression/constantinteger.h"
#include "JavaScriptCore/symbolic/expression/constantstring.h"
#include "JavaScriptCore/symbolic/expression/stringcoercion.h"
#include "JavaScriptCore/symbolic/expression/integercoercion.h"
#include "JavaScriptCore/symbolic/expression/stringbinaryoperation.h"

#include "symbolicinterpreter.h"

#ifdef ARTEMIS

namespace Symbolic
{

const char* opToString(OP op) {
    static const char* OPStrings[] = {
        "==", "!=", "===", "!==", "<=", "<", ">=", ">",
        "+", "-", "*", "/" "%"
    };

    return OPStrings[op];
}

SymbolicInterpreter::SymbolicInterpreter() :
    m_nextSymbolicValue(0),
    m_shouldGC(false)
{
}

void SymbolicInterpreter::ail_call(JSC::CallFrame*, const JSC::Instruction*, JSC::BytecodeInfo&)
{
}

void SymbolicInterpreter::ail_call_native(JSC::CallFrame* callFrame, const JSC::Instruction*, JSC::BytecodeInfo&,
                                          JSC::native_function_ID_t functionID)
{
    const NativeFunction* nativeFunction = m_nativeFunctions.find(functionID);

    if (nativeFunction == NULL) {
        //std::cout << "AIL_CALL_NATIVE <Unknown native function>" << std::endl;
        return;
    }

    //std::cout << "AIL_CALL_NATIVE <" << nativeFunction->getName() << ">" << std::endl;
}

JSC::JSValue SymbolicInterpreter::ail_op_binary(JSC::CallFrame* callFrame, const JSC::Instruction*, JSC::BytecodeInfo& info,
                                                JSC::JSValue& x, OP op, JSC::JSValue& y,
                                                JSC::JSValue result)
{

    if (!x.isSymbolic() && !y.isSymbolic()) {
        return result; // not symbolic
    }

    info.setSymbolic();

    switch (op) {

    case EQUAL:
    case NOT_EQUAL:
        break;

    case STRICT_EQUAL:
    case NOT_STRICT_EQUAL:
        break;

    case LESS_EQ:
    case LESS_STRICT:
        break;

    case GREATER_EQ:
    case GREATER_STRICT:
        break;

    case ADD:
    case SUBTRACT: {

        // case 1: number
        if (x.isNumber() && y.isNumber()) {

            Symbolic::IntegerExpression* sx = x.isSymbolic() ? (Symbolic::IntegerExpression*)x.asSymbolic() : new ConstantInteger(x.asNumber());
            Symbolic::IntegerExpression* sy = y.isSymbolic() ? (Symbolic::IntegerExpression*)y.asSymbolic() : new ConstantInteger(y.asNumber());

            result.makeSymbolic(new IntegerBinaryOperation(sx, INT_ADD, sy));

            ASSERT(result.isSymbolic());

            return result;
        }

        // case 2: string
        if (x.isString()) {

            Symbolic::StringExpression* sx = NULL;
            Symbolic::StringExpression* sy = NULL;

            sx = x.isSymbolic() ? (Symbolic::StringExpression*)x.asSymbolic() : new ConstantString(x.toString(callFrame));

            if (y.isString()) {
                sy = y.isSymbolic() ? (Symbolic::StringExpression*)y.asSymbolic() : new ConstantString(y.toString(callFrame));
            } else {
                // y string coercion
                sy = y.isSymbolic() ? (Symbolic::StringExpression*)new StringCoercion(y.asSymbolic()) :
                                      (Symbolic::StringExpression*)new ConstantString(y.toPrimitiveString(callFrame)->toString(callFrame));
            }

            ASSERT(sx != NULL);
            ASSERT(sy != NULL);

            result.makeSymbolic(new StringBinaryOperation(sx, CONCAT, sy));

            ASSERT(result.isSymbolic());

            return result;
        }

        JSC::JSValue xx = x.toPrimitive(callFrame);
        JSC::JSValue yy = y.toPrimitive(callFrame);

        // case 3: primitive string
        if (xx.isString()) {

            Symbolic::StringExpression* sx = NULL;
            Symbolic::StringExpression* sy = NULL;

            sx = x.isSymbolic() ? (Symbolic::StringExpression*)x.asSymbolic() : new ConstantString(xx.toString(callFrame));

            if (yy.isString()) {
                sy = y.isSymbolic() ? (Symbolic::StringExpression*)y.asSymbolic() : new ConstantString(yy.toString(callFrame));

            } else {
                // yy string coercion
                sy = y.isSymbolic() ? (Symbolic::StringExpression*)new StringCoercion(y.asSymbolic()) :
                                      (Symbolic::StringExpression*)new ConstantString(yy.toString(callFrame));
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

            sx = x.isSymbolic() ? (Symbolic::StringExpression*)new StringCoercion(x.asSymbolic()) :
                                  (Symbolic::StringExpression*)new ConstantString(xx.toString(callFrame));
            sy = y.isSymbolic() ? (Symbolic::StringExpression*)y.asSymbolic() : new ConstantString(yy.toString(callFrame));

            ASSERT(sx != NULL);
            ASSERT(sy != NULL);

            result.makeSymbolic(new StringBinaryOperation(sx, CONCAT, sy));

            ASSERT(result.isSymbolic());

            return result;
        }

        // case 4: primitive number coercion

        Symbolic::IntegerExpression* sx = NULL;
        Symbolic::IntegerExpression* sy = NULL;

        if (xx.isNumber()) {
            sx = x.isSymbolic() ? (Symbolic::IntegerExpression*)x.asSymbolic() : new ConstantInteger(xx.asNumber());
        } else {
            sx = x.isSymbolic() ? (Symbolic::IntegerExpression*)new IntegerCoercion(x.asSymbolic()) :
                                  (Symbolic::IntegerExpression*)new ConstantInteger(xx.asNumber());
        }

        if (yy.isNumber()) {
            sy = y.isSymbolic() ? (Symbolic::IntegerExpression*)y.asSymbolic() : new ConstantInteger(yy.asNumber());
        } else {
            sy = y.isSymbolic() ? (Symbolic::IntegerExpression*)new IntegerCoercion(y.asSymbolic()) :
                                  (Symbolic::IntegerExpression*)new ConstantInteger(yy.asNumber());
        }

        ASSERT(sx != NULL);
        ASSERT(sy != NULL);

        result.makeSymbolic(new IntegerBinaryOperation(sx, INT_ADD, sy));

        ASSERT(result.isSymbolic());

        return result;
    }

    case MULTIPLY:
        break;

    case DIVIDE:
        break;

    case MODULO:
        break;

    }

    //std::string xValue = x.isSymbolic() ? x.asSymbolic()->value : std::string(x.toString(callFrame).ascii().data());
    //std::string yValue = y.isSymbolic() ? y.asSymbolic()->value : std::string(y.toString(callFrame).ascii().data());

    //std::string value = std::string("(") + xValue + std::string(opToString(op)) + yValue + std::string(")");

    //std::cout << "AIL_OP_BINARY " << value << std::endl;

    return result;
}

void SymbolicInterpreter::ail_jmp_iff(JSC::CallFrame* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info,
                                      JSC::JSValue& condition, bool jumps)
{
    if (condition.isSymbolic()) {
        info.setSymbolic();
        //std::cout << "AIL_JMP_IFF " << condition.asSymbolic()->value << std::endl;
    } else {
        //std::cout << "AIL_JMP_IFF" << std::endl;
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
}

void SymbolicInterpreter::endSession()
{
}

}

#endif
