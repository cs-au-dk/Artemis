#ifdef ARTEMIS
#include <config.h>

#include "listenerdebugger.h"
#include "executionlistener.h"

namespace inst {

    ListenerDebugger::ListenerDebugger(ExecutionListener* ll) {
        el = ll;
    }

    void ListenerDebugger::sourceParsed(JSC::ExecState* es, const JSC::SourceCode& sc, int errorLineNumber, const JSC::UString& errorMessage) {
        el->loadJavaScript(sc,es);
    }
    void ListenerDebugger::exception(const JSC::DebuggerCallFrame& frame, intptr_t sourceID, int lineNumber, bool hasHandler) {
        if (!hasHandler) {
            el->exceptional_condition("TODO: Get error text!",sourceID,lineNumber);
        }
    }
    void ListenerDebugger::atStatement(const JSC::DebuggerCallFrame& frame, intptr_t sourceID, int lineNumber){
        el->interpreterExecutedStatement(frame, sourceID, lineNumber);
    }
    void ListenerDebugger::callEvent(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber){}
    void ListenerDebugger::returnEvent(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber){}
    void ListenerDebugger::willExecuteProgram(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber){}
    void ListenerDebugger::didExecuteProgram(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber){}
    void ListenerDebugger::didReachBreakpoint(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber){}
}
#endif
