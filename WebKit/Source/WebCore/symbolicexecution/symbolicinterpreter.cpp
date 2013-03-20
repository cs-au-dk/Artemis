
#include <iostream>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"

#include "symbolicinterpreter.h"

#ifdef ARTEMIS

namespace SymbolicExecution
{

SymbolicInterpreter::SymbolicInterpreter() : ArtemisIL()
{
}

void SymbolicInterpreter::ail_call(JSC::CodeBlock*)
{
    std::cout << "AIL_CALL" << std::endl;
}

void SymbolicInterpreter::ail_call_native(JSC::CodeBlock* codeBlock, JSC::native_function_ID_t functionID)
{
    const NativeFunction* nativeFunction = mNativeFunctions.find(functionID);

    if (nativeFunction == NULL) {
        fatalError(codeBlock, "Unknown native function encountered");
    }

    std::cout << "AIL_CALL_NATIVE <" << nativeFunction->getName() << ">" << std::endl;
}

void SymbolicInterpreter::fatalError(JSC::CodeBlock* codeBlock, std::string reason)
{
    std::cerr << reason << std::endl;
    exit(1);
}

}

#endif
