#ifdef ARTEMIS

#include <stdint.h>
#include <string>

#ifndef EXECUTIONLISTENER_H
#define EXECUTIONLISTENER_H

namespace WebCore {
    class EventTarget;
    class Frame;
    class DOMWindow;
    class Node;
    class XMLHttpRequest;
    class ScriptExecutionContext;
    class LazyXMLHttpRequest;
}

namespace JSC {
    class Debugger;
    class SourceProvider;
    struct DebuggerCallFrame;
    class JSValue;
    class ExecState;
}

namespace inst {

    class ListenerDebugger;

    class ExecutionListener {
    public:
        ExecutionListener();
        /**
          Invoked when an event is added to a DOM element
          */
        void eventAdded(WebCore::EventTarget *, const char*);
        virtual void domWindowEventAdded(WebCore::DOMWindow*, const std::string);
        virtual void nodeEventAdded(WebCore::Node*, const std::string);

        /**
          Invoked when a dom element no longer has events attached.
          */
        void eventCleared(WebCore::EventTarget *, const char*);
        virtual void domWindowEventCleared(WebCore::DOMWindow*, const std::string);
        virtual void nodeEventCleared(WebCore::Node*, const std::string);

        /**
         * Timeouts
         */
        virtual void timerAdded(WebCore::ScriptExecutionContext* context, int timerId, int timeout, bool singleShot);
        virtual void timerRemoved(WebCore::ScriptExecutionContext* context, int timerId);

        /**
          Loading of files
          */
        void loadJavaScript(JSC::SourceProvider* sp, JSC::ExecState*);
        virtual void scriptCodeLoaded(intptr_t id,std::string source, std::string url ,int startline);

        /**
          Coverage information
          */
        void interpreterExecutedStatement(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);
        virtual void executedStatement(intptr_t sourceID, std::string function_name, int linenumber);


        /** 
          Function calls
          */
        void interpreterCalledEvent(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);
        virtual void calledFunction(const JSC::DebuggerCallFrame&);

        /**
          Exception
          */
        virtual void exceptional_condition(std::string cause, intptr_t sourceID, int lineNumber);

        /**
          Url changing
          */
        void url_changed( JSC::JSValue,  JSC::ExecState* e);
        virtual void script_changed_url( std::string url);

        /**
          Ajax
          */
        virtual void webkit_ajax_send(const char * url, const char * data);
        virtual void ajaxCallbackEventAdded(WebCore::LazyXMLHttpRequest*);

        /**
          Eval
          */
        virtual void webkit_eval_call(const char * eval_string);
    };


    extern ExecutionListener* dummy_listener;
    extern ExecutionListener* default_listener;

    ExecutionListener* getDummy();
    ExecutionListener* getDefaultListener();
    void setDefaultListener(ExecutionListener*);

    ListenerDebugger* getDebugger();
}
#endif // EXECUTIONLISTENER_H
#endif
