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

#ifndef SYMBOLICINTERPRETER_H
#define SYMBOLICINTERPRETER_H

#include <sstream>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/runtime/CallData.h"
#include "JavaScriptCore/instrumentation/bytecodeinfo.h"

#include "pathcondition.h"
#include "native/nativelookup.h"

#ifdef ARTEMIS

#define SSTR(x) dynamic_cast< std::ostringstream & >( \
        ( std::ostringstream() << std::dec << x ) ).str()

namespace JSC {
    class ExecState;
    class Instruction;
}

namespace Symbolic
{

typedef enum {
    EQUAL, NOT_EQUAL, STRICT_EQUAL, NOT_STRICT_EQUAL, LESS_EQ, LESS_STRICT, GREATER_EQ, GREATER_STRICT,
    ADD, SUBTRACT, MULTIPLY, DIVIDE, MODULO
} OP;

const char* opToString(OP op);

WTF_EXPORT_PRIVATE class SymbolicInterpreter
{

public:
    SymbolicInterpreter();

    void ail_call(JSC::CallFrame* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info);
    void ail_call_native(JSC::CallFrame* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info,
                         JSC::native_function_ID_t functionID);

    JSC::JSValue ail_op_binary(JSC::CallFrame* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info,
                               JSC::JSValue& x, OP op, JSC::JSValue& y, JSC::JSValue result);

    void ail_jmp_iff(JSC::CallFrame* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info,
                     JSC::JSValue& condition, bool jumps);

    // called from the interpreter before it starts executing (a single trace)
    void preExecution(JSC::CallFrame* callFrame);

    // called from Artemis
    void beginSession();
    void endSession();
    PathCondition* getPathCondition();
    std::string generatePathConditionString();

private:
    void fatalError(JSC::CodeBlock* codeBlock, std::string reason) __attribute__((noreturn));

    PathCondition m_pc;

    NativeLookup m_nativeFunctions;
    int m_nextSymbolicValue;

    bool m_shouldGC;
};

}

#endif
#endif // SYMBOLICINTERPRETER_H
