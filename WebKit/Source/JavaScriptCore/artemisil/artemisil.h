#ifndef ARTEMISIL_H
#define ARTEMISIL_H

#include <inttypes.h>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/runtime/CallData.h"

#ifdef ARTEMIS

namespace JSC {
    class ExecState;
    class Instruction;
}

namespace JSC
{

typedef intptr_t native_function_ID_t;

class ArtemisIL
{

public:
    ArtemisIL();

    virtual void ail_call(ExecState* callFrame, const Instruction* vPC) = 0;
    virtual void ail_call_native(ExecState* callFrame, const Instruction* vPC, native_function_ID_t functionID) = 0;

};

}

#endif
#endif // ARTEMISIL_H
