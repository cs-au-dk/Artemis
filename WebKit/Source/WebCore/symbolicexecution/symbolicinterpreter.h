#ifndef SYMBOLICINTERPRETER_H
#define SYMBOLICINTERPRETER_H

#include "JavaScriptCore/artemisil/artemisil.h"

#include "native/nativelookup.h"

#ifdef ARTEMIS

namespace SymbolicExecution
{

class SymbolicInterpreter : public JSC::ArtemisIL
{

public:
    SymbolicInterpreter();

    void ail_call(JSC::CallFrame* callFrame, const JSC::Instruction* vPC);
    void ail_call_native(JSC::CallFrame* callFrame, const JSC::Instruction* vPC,
                         JSC::native_function_ID_t functionID);

private:
    void fatalError(JSC::CodeBlock* codeBlock, std::string reason) __attribute__((noreturn));

    NativeLookup mNativeFunctions;
};

}

#endif
#endif // SYMBOLICINTERPRETER_H
