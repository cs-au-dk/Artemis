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
#include "JavaScriptCore/symbolic/expression/constantboolean.h"
#include "JavaScriptCore/symbolic/expression/stringcoercion.h"
#include "JavaScriptCore/symbolic/expression/integercoercion.h"
#include "JavaScriptCore/symbolic/expression/stringbinaryoperation.h"
#include "JavaScriptCore/symbolic/expression/booleanbinaryoperation.h"

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

Symbolic::IntegerExpression* generateIntegerExpression(JSC::JSValue& val, JSC::CallFrame* callFrame){
    return val.isSymbolic()?(Symbolic::IntegerExpression*)val.asSymbolic() : new ConstantInteger(val.toPrimitive(callFrame).asNumber());
}

Symbolic::StringExpression* generateStringExpression(JSC::JSValue& val, JSC::CallFrame* callFrame){
    return val.isSymbolic()?(Symbolic::StringExpression*) val.asSymbolic(): new ConstantString(val.toPrimitive(callFrame).toString(callFrame));
}

Symbolic::IntegerExpression* generateIntegerCoercionExpression(JSC::JSValue& val, JSC::CallFrame* callFrame){
    return val.isSymbolic() ? (Symbolic::IntegerExpression*)new IntegerCoercion(val.asSymbolic()) : new ConstantInteger(val.toPrimitive(callFrame).toNumber(callFrame));
}

Symbolic::StringExpression* generateStringCoercionExpression(JSC::JSValue& val, JSC::CallFrame* callFrame){
    return val.isSymbolic() ? (Symbolic::StringExpression*)new StringCoercion(val.asSymbolic()) :
                            (Symbolic::StringExpression*)new ConstantString(val.toPrimitiveString(callFrame)->toString(callFrame));
}

Symbolic::BooleanExpression* generateBooleanExpression(JSC::JSValue& val, JSC::CallFrame* callFrame){
    return val.isSymbolic()?(Symbolic::BooleanExpression*) val.asSymbolic():new ConstantBoolean(val.toPrimitive(callFrame).toBoolean(callFrame));
}


JSC::JSValue SymbolicInterpreter::ail_op_binary(JSC::CallFrame* callFrame, const JSC::Instruction*, JSC::BytecodeInfo& info,
                                                JSC::JSValue& x, OP op, JSC::JSValue& y,
                                                JSC::JSValue result)
{

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

            Symbolic::IntegerExpression* sx = generateIntegerExpression(x, callFrame);
            Symbolic::IntegerExpression* sy = generateIntegerExpression(y, callFrame);

            result.makeSymbolic(new IntegerBinaryOperation(sx, neq?INT_NEQ:INT_EQ, sy));

            ASSERT(result.isSymbolic());

            return result;

        }


        // Case 2: String
        if (xx.isString() && yy.isString()) {
            Symbolic::StringExpression* sx = generateStringExpression(x,callFrame);
            Symbolic::StringExpression* sy = generateStringExpression(y,callFrame);

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
            Symbolic::BooleanExpression* sx = generateBooleanExpression(x,callFrame);
            Symbolic::BooleanExpression* sy = generateBooleanExpression(y,callFrame);
            result.makeSymbolic(new BooleanBinaryOperation(sx,neq?BOOL_NEQ:BOOL_EQ,sy));
            return result;
        }

        // Case 4: Mixed string and <other>
        if (xx.isString() || yy.isString() || xx.isBoolean() || yy.isBoolean()) {

            Symbolic::IntegerExpression* sx = NULL;
            Symbolic::IntegerExpression* sy = NULL;

            sx = x.isNumber()? generateIntegerExpression(x, callFrame):generateIntegerCoercionExpression(x,callFrame);
            sy = y.isNumber()? generateIntegerExpression(y, callFrame):generateIntegerCoercionExpression(y,callFrame);

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
            Symbolic::StringExpression* sx = generateStringExpression(x, callFrame);
            Symbolic::StringExpression* sy = generateStringExpression(y, callFrame);
            result.makeSymbolic(new StringBinaryOperation(sx,neq?STRING_SNEQ:STRING_SEQ,sy));
            return result;
        }

        if(x.isNumber() && y.isNumber()){
            Symbolic::IntegerExpression* sx = generateIntegerExpression(x,callFrame);
            Symbolic::IntegerExpression* sy = generateIntegerExpression(y,callFrame);
            result.makeSymbolic(new IntegerBinaryOperation(sx,neq?INT_SNEQ:INT_SEQ,sy));
            return result;
        }

        if(x.isBoolean() && y.isBoolean()){
            Symbolic::BooleanExpression* sx = generateBooleanExpression(x,callFrame);
            Symbolic::BooleanExpression* sy = generateBooleanExpression(y,callFrame);
            result.makeSymbolic(new BooleanBinaryOperation(sx,neq?BOOL_SNEQ:BOOL_SEQ,sy));
            return result;
        }


        break;
    case LESS_EQ:
        intOp = INT_LEQ;
        strOp = STRING_LEQ;
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
            Symbolic::StringExpression* sx = generateStringExpression(x,callFrame);
            Symbolic::StringExpression* sy = generateStringExpression(x,callFrame);
            result.makeSymbolic(new StringBinaryOperation(sx,strOp,sy));
            return result;
        }
        Symbolic::IntegerExpression* sx = xx.isNumber()?generateIntegerExpression(x,callFrame):generateIntegerCoercionExpression(x,callFrame);
        Symbolic::IntegerExpression* sy = yy.isNumber()?generateIntegerExpression(y,callFrame):generateIntegerCoercionExpression(y,callFrame);
        result.makeSymbolic(new IntegerBinaryOperation(sx,intOp,sy));
        return result;
        break;
}


    case ADD: {

        // case 1: number
        if (x.isNumber() && y.isNumber()) {

            Symbolic::IntegerExpression* sx = generateIntegerExpression(x, callFrame);
            Symbolic::IntegerExpression* sy = generateIntegerExpression(y, callFrame);

            ASSERT(sx);
            ASSERT(sy);

            result.makeSymbolic(new IntegerBinaryOperation(sx, INT_ADD, sy));

            ASSERT(result.isSymbolic());

            return result;
        }
        JSC::JSValue xx = x.toPrimitive(callFrame);
        JSC::JSValue yy = y.toPrimitive(callFrame);

        // case 2: string
        if (x.isString() || xx.isString()) {

            Symbolic::StringExpression* sx = NULL;
            Symbolic::StringExpression* sy = NULL;

            sx = generateStringExpression(x,callFrame);

            if (y.isString() || yy.isString()) {
                sy = generateStringExpression(y,callFrame);
            } else {
                // y string coercion
                sy = generateStringCoercionExpression(y,callFrame);
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

            sx = generateStringCoercionExpression(x, callFrame);
            sy = generateStringExpression(y,callFrame);

            ASSERT(sx != NULL);
            ASSERT(sy != NULL);

            result.makeSymbolic(new StringBinaryOperation(sx, CONCAT, sy));

            ASSERT(result.isSymbolic());

            return result;
        }

        // case 4: primitive number coercion

        Symbolic::IntegerExpression* sx = NULL;
        Symbolic::IntegerExpression* sy = NULL;

        sx = xx.isNumber()? generateIntegerExpression(x,callFrame):generateIntegerCoercionExpression(x,callFrame);
        sy = yy.isNumber()? generateIntegerExpression(y,callFrame):generateIntegerCoercionExpression(y,callFrame);

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
        sx = generateIntegerExpression(x,callFrame);
        sy = generateIntegerExpression(y, callFrame);

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

void SymbolicInterpreter::ail_jmp_iff(JSC::CallFrame* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info,
                                      JSC::JSValue& condition, bool jumps)
{
    if (condition.isSymbolic()) {
        info.setSymbolic();
        m_pc.append(condition.asSymbolic());
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
    std::cout << "PC size: " << m_pc.size() << std::endl;
}

}

#endif
