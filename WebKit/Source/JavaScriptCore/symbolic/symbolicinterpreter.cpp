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

#include "symbolic/sources/forminputsource.h"

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
    m_shouldTaint(false),
    m_shouldGC(false),
    m_initial(true)
{
}

void SymbolicInterpreter::ail_call(JSC::CallFrame*, const JSC::Instruction*, JSC::BytecodeInfo&)
{
    //std::cout << "AIL_CALL" << std::endl;
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

    /* Symbolic */

    if (!x.isSymbolic() && !y.isSymbolic()) {
        return result; // not symbolic
    }

    info.setSymbolic();

    std::string xValue = x.isSymbolic() ? x.asSymbolic()->value : std::string(x.toString(callFrame).ascii().data());
    std::string yValue = y.isSymbolic() ? y.asSymbolic()->value : std::string(y.toString(callFrame).ascii().data());

    std::string value = std::string("(") + xValue + std::string(opToString(op)) + yValue + std::string(")");

    //std::cout << "AIL_OP_BINARY " << value << std::endl;

    result.makeSymbolic(value);
    ASSERT(result.isSymbolic());

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
    if (m_initial) {
        JSC::JSGlobalData* jsGlobalData = &callFrame->globalData();
        JSC::Heap* heap = &jsGlobalData->heap;

        heap->notifyIsNotSafeToCollect();

        //m_nativeFunctions.buildRegistry(callFrame);

        m_initial = false;
    }

    if (m_shouldGC) {
        JSC::JSGlobalData* jsGlobalData = &callFrame->globalData();
        JSC::Heap* heap = &jsGlobalData->heap;

        heap->notifyIsSafeToCollect();
        heap->collectAllGarbage();
        heap->notifyIsNotSafeToCollect();

        m_shouldGC = false;
    }

    if (m_shouldTaint) {

        std::cout << "TAINT" << std::endl;
        DomTraversal::traverseDom(callFrame, new FormInputSource());
        std::cout << "TAINT" << std::endl;
        m_shouldTaint = false;
    }
}

void SymbolicInterpreter::beginSession()
{
    m_shouldTaint = true;
}

void SymbolicInterpreter::endSession()
{
    m_shouldGC = true;
}

}

#endif
