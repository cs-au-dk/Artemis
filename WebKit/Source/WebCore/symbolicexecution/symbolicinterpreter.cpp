
#include <iostream>
#include <tr1/unordered_set>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"

#include "symbolicinterpreter.h"

namespace SymbolicExecution
{

SymbolicInterpreter::SymbolicInterpreter() : ArtemisIL()
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

void SymbolicInterpreter::fatalError(JSC::CodeBlock* codeBlock, std::string reason)
{
    std::cerr << reason << std::endl;
    exit(1);
}

}
