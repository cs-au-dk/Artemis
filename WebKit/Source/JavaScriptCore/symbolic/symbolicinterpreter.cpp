
#include <iostream>
#include <tr1/unordered_set>
#include <inttypes.h>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"

#include "symbolicinterpreter.h"

namespace Symbolic
{

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

JSC::SymbolicValue* SymbolicInterpreter::ail_op_binary(JSC::CallFrame* callFrame, const JSC::Instruction* vPC,
                                        JSC::JSValue& x, OP op, JSC::JSValue& y)
{
    if (!x.isSymbolic()) {
        x.mutateSymbolic(mNextSymbolicValue++, "");
        ASSERT(x.isSymbolic());
    }

    if (!y.isSymbolic()) {
        y.mutateSymbolic(mNextSymbolicValue++, "");
        ASSERT(y.isSymbolic());
    }

    std::string value = std::string("<") + std::string(SSTR(x.asSymbolic()->identifier)) + std::string("> OP <") + std::string(SSTR(y.asSymbolic()->identifier)) + std::string(">");

    std::cout << "AIL_OP_BINARY " << value << std::endl;

    return new JSC::SymbolicValue(mNextSymbolicValue++, value);
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
