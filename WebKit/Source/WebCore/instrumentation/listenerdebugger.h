#ifdef ARTEMIS
#ifndef LISTENERDEBUGGER_H
#define LISTENERDEBUGGER_H

#include <JavaScriptCore/debugger/Debugger.h>
#include <stdint.h>
#include "executionlistener.h"

namespace JSC {

    class DebuggerCallFrame;
    class ExecState;
    class JSGlobalData;
    class JSGlobalObject;
    class JSValue;
    class SourceCode;
    class UString;

}

namespace inst {

    class ListenerDebugger : public JSC::Debugger
    {
    public:
        ListenerDebugger(ExecutionListener*);

        void sourceParsed(JSC::ExecState*, const JSC::SourceCode&, int errorLineNumber, const JSC::UString& errorMessage);
        void exception(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber, bool hasHandler);
        void atStatement(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);
        void callEvent(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);
        void returnEvent(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);

        void willExecuteProgram(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);
        void didExecuteProgram(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);
        void didReachBreakpoint(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);

    private:
        ExecutionListener* el;

    };

}
#endif // LISTENERDEBUGGER_H
#endif
