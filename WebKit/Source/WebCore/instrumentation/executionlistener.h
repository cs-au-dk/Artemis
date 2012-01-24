#ifdef ARTEMIS
#ifndef EXECUTIONLISTENER_H
#define EXECUTIONLISTENER_H

#include <string>

namespace WebCore {
    class EventTarget;
    class Frame;
    class DOMWindow;
    class Node;
}

namespace JSC {
    class Debugger;
    class SourceProvider;
    class ExecState;
    class DebuggerCallFrame;
    class JSValue;
}

namespace inst {

    class ListenerDebugger;

    class ExecutionListener {
    public:
        ExecutionListener();
        /**
          Invoked when an event is added to a DOM element
          */
        void eventAdded( WebCore::EventTarget *, const char*);
        virtual void domWindowEventAdded( WebCore::DOMWindow*, const std::string);
        virtual void nodeEventAdded( WebCore::Node*, const std::string);
        /**
          Invoked when a dom element no longer has events attached.
          */
        void eventCleared( WebCore::EventTarget *, const char*);
        virtual void  domWindowEventCleared(WebCore::DOMWindow*, const std::string);
        virtual void nodeEventCleared(WebCore::Node*, const std::string);

        /**
          Loading of files
          */
        void loadJavaScript(JSC::SourceProvider* sp, JSC::ExecState*);
        virtual void scriptCodeLoaded(intptr_t id,std::string source, std::string url ,int startline);

        /**
          Coverage information
          */
        void interpreterExecutedStatement(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);
        void interpreterCalledEvent(const JSC::DebuggerCallFrame&, intptr_t sourceID, int lineNumber);
        virtual void executedStatement(intptr_t sourceID, std::string function_name, int linenumber);

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
