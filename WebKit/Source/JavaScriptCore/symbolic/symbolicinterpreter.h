#ifndef SYMBOLICINTERPRETER_H
#define SYMBOLICINTERPRETER_H

#include <sstream>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/runtime/CallData.h"

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
    ADD, SUBTRACT, MILTIPLY, DIVIDE, MODULO
} OP;

class SymbolicInterpreter
{

public:
    SymbolicInterpreter();

    void ail_call(JSC::CallFrame* callFrame, const JSC::Instruction* vPC);
    void ail_call_native(JSC::CallFrame* callFrame, const JSC::Instruction* vPC,
                         JSC::native_function_ID_t functionID);

    JSC::SymbolicValue* ail_op_binary(JSC::CallFrame* callFrame, const JSC::Instruction* vPC,
                                      JSC::JSValue& x, OP op, JSC::JSValue& y);
    void ail_jmp_iff(JSC::CallFrame* callFrame, const JSC::Instruction* vPC,
                     const JSC::JSValue& condition);

    void beginSession();
    void endSession();

private:
    void fatalError(JSC::CodeBlock* codeBlock, std::string reason) __attribute__((noreturn));

    NativeLookup mNativeFunctions;

    std::string mPC;
    int mNextSymbolicValue;
};

}

#endif
#endif // SYMBOLICINTERPRETER_H
