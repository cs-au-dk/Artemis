
#include <iostream>
#include <tr1/unordered_set>
#include <inttypes.h>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"

#include "symbolicinterpreter.h"
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
    mPC(""),
    mNextSymbolicValue(0)
{
}

void SymbolicInterpreter::ail_call(JSC::CallFrame*, const JSC::Instruction*)
{
    std::cout << "AIL_CALL" << std::endl;
}

void SymbolicInterpreter::ail_call_native(JSC::CallFrame* callFrame, const JSC::Instruction*,
                                          JSC::native_function_ID_t functionID)
{
    // We should find a much better place to call this (and only call it once)
    mNativeFunctions.buildRegistry(callFrame);

    const NativeFunction* nativeFunction = mNativeFunctions.find(functionID);

    if (nativeFunction == NULL) {
        std::cout << "AIL_CALL_NATIVE <Unknown native function>" << std::endl;
        return;
    }

    std::cout << "AIL_CALL_NATIVE <" << nativeFunction->getName() << ">" << std::endl;
}

JSC::JSValue SymbolicInterpreter::ail_op_binary(JSC::CallFrame*, const JSC::Instruction*,
                                                JSC::JSValue& x, OP op, JSC::JSValue& y,
                                                JSC::JSValue result)
{
    if (!x.isSymbolic()) {
        x.mutateSymbolic(std::string("<") + SSTR(mNextSymbolicValue++) + std::string(">"));
        ASSERT(x.isSymbolic());
    }

    if (!y.isSymbolic()) {
        y.mutateSymbolic(std::string("<") + SSTR(mNextSymbolicValue++) + std::string(">"));
        ASSERT(y.isSymbolic());
    }

    std::string value = std::string("(") + x.asSymbolic()->value + std::string(opToString(op)) + y.asSymbolic()->value + std::string(")");

    std::cout << "AIL_OP_BINARY " << value << std::endl;

    result.mutateSymbolic(value);
    ASSERT(result.isSymbolic());

    return result;
}

void SymbolicInterpreter::ail_jmp_iff(JSC::CallFrame* callFrame, const JSC::Instruction* vPC,
                                      const JSC::JSValue& condition)
{
    if (condition.isSymbolic()) {
        std::cout << "AIL_JMP_IFF " << condition.asSymbolic()->value << std::endl;
    } else {
        std::cout << "AIL_JMP_IFF" << std::endl;
    }

}

void SymbolicInterpreter::fatalError(JSC::CodeBlock* codeBlock, std::string reason)
{
    std::cerr << reason << std::endl;
    exit(1);
}

void SymbolicInterpreter::beginSession()
{
    std::cout << "Symbolic Session START" << std::endl;
    mPC = "";
    mNextSymbolicValue = 0;
}

void SymbolicInterpreter::endSession()
{
    std::cout << "Symbolic Session END" << std::endl;
    std::cout << "PC = " << mPC << std::endl;
}

}

#endif
