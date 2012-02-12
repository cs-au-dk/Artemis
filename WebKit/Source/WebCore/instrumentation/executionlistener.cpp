#ifdef ARTEMIS

#include <stdlib.h>
#include <iostream>
#include <config.h>
#include <JSValue.h>
#include <JSObject.h>
#include <UString.h>
#include <dom/EventTarget.h>
#include <wtf/text/CString.h>
#include "JavaScriptCore/parser/SourceCode.h"

#include "JavaScriptCore/debugger/DebuggerCallFrame.h"
#include "JavaScriptCore/interpreter/CallFrame.h"
#include "JavaScriptCore/instrumentation/jscexecutionlistener.h"
#include "WebCore/instrumentation/jscriptlistenerclient.h"
#include "WebCore/instrumentation/listenerdebugger.h"
#include "JavaScriptCore/runtime/Identifier.h"
#include "JavaScriptCore/runtime/ScopeChain.h"
#include "JavaScriptCore/interpreter/Register.h"

#include "executionlistener.h"

namespace inst {


    ExecutionListener::ExecutionListener()
    {
        jsinst::JSCExecutionListener* ll = new JScriptListenerClient(this);
        jsinst::initialize_js_listener(ll);
    }

    void ExecutionListener::eventAdded(WebCore::EventTarget * e, const char* type) {
        std::string s = std::string(type);
        
        if (e->toNode() != NULL)
            nodeEventAdded(e->toNode(), s);
        else if (e->toDOMWindow() != NULL)
            domWindowEventAdded(e->toDOMWindow(), s);
        else
            std::cout << "ERROR: Strange event :" << s << std::endl;
        return;
    }

    void ExecutionListener::eventCleared(WebCore::EventTarget * e, const char* type) {
        std::string s = std::string(type);
        std::cout << "el::event cleared: " << s << std::endl;

    }

    void ExecutionListener::domWindowEventCleared(WebCore::DOMWindow *, const std::string) {
        std::cout << "el::dom event cleared" << std::endl;
        return;
    }

    void ExecutionListener::nodeEventCleared(WebCore::Node * , const std::string) {
        std::cout << "el::node event cleared" <<std::endl;
        return;
    }

    void ExecutionListener::domWindowEventAdded( WebCore::DOMWindow * window, const std::string type) {
        return;
    }

    void ExecutionListener::nodeEventAdded( WebCore::Node * node, const std::string type) {
        return;
    }

    ExecutionListener* dummy_listener = new ExecutionListener();
    ExecutionListener* default_listener;
    ListenerDebugger* debugger;

    ExecutionListener* getDummy() {
        return dummy_listener;
    }

    ExecutionListener* getDefaultListener() {
        if (default_listener == NULL)
            return dummy_listener;
        return default_listener;
    }

    void setDefaultListener(ExecutionListener* e) {
        std::cout << "WEBKIT: Execution listener was set..." << std::endl;
        default_listener = e;
    }

    ListenerDebugger* getDebugger() {
        if (debugger == NULL) {
            debugger = new ListenerDebugger(getDefaultListener());
        }
        return debugger;
    }

    void ExecutionListener::loadJavaScript(JSC::SourceProvider* sp, JSC::ExecState* es) {
        // SourceProvider has changed API lately, thus the following usage of it has not been fully
        // tested with artemis - e.g. if you are tracking an error and reach this point, then you
        // have come to the right place.

        std::string source(sp->getRange(0, sp->length()).utf8().data());
        std::string url(sp->url().utf8().data());
        intptr_t id = sp->asID();
        int fl = 1;

        scriptCodeLoaded(id, source, url, fl);
    }

    void ExecutionListener::scriptCodeLoaded(intptr_t id, std::string source, std::string url, int startline) {
        std::cout << "el::load from " << url << " [" << startline << "]" << std::endl;
        std::cout << "el::loaded script: " << source << std::endl;
    }

    void ExecutionListener::interpreterExecutedStatement(const JSC::DebuggerCallFrame& frame, intptr_t sourceID, int lineNumber) {
        /* std::string(frame.calculatedFunctionName().ascii().data()) */
        /* FIXME IMPORTANT */
        executedStatement(sourceID, "fooBar()", lineNumber);
    }

    void ExecutionListener::executedStatement(intptr_t sourceID, std::string function_name, int linenumber) {
        //EMPTY
    }

    void ExecutionListener::interpreterCalledEvent(const JSC::DebuggerCallFrame& frame, intptr_t sourceID, int lineNumber) {
        calledFunction(frame);

        /* JQuery SUPPORT */
        /*JSC::JSGlobalData * globalData = &cframe->globalData();*/
   
        /*
        JSC::IdentifierTable * identifierTable = cframe->globalData().identifierTable;
        JSC::LiteralIdentifierTable literalIdentifierTable = identifierTable->literalTable();

        const JSC::LiteralIdentifierTable::iterator& iter = literalIdentifierTable.find("omgtest");
        if (iter != literalIdentifierTable.end()) {
            std::cout << "el::JQUERY SCRIPT DETECTED!!!!!" << std::endl;
        } else { 
            std::cout << "el::not JQuery script" << std::endl;
        }
        */
    }

    void ExecutionListener::calledFunction(const JSC::DebuggerCallFrame&) {
        // EMPTY
    }

    void ExecutionListener::exceptional_condition(std::string cause, intptr_t sourceID, int lineNumber) {
        std::cout << "el::program crash: " << cause << " at " << lineNumber << std::endl;
    }

    void ExecutionListener::url_changed(JSC::JSValue v,  JSC::ExecState* e) {
        std::string url;
        if (v.isString()) {
            url = std::string(v.getString(e).utf8().data());
        } else {
            url = std::string(v.toString(e).utf8().data());
        }
        this->script_changed_url(url);
    }

    void ExecutionListener::script_changed_url( std::string url) {
        std::cout << "el::script_changed_url : " << url;
    }

    void ExecutionListener::webkit_ajax_send(const char * url, const char * data) {

    }

    void ExecutionListener::webkit_eval_call(const char * eval_string) {

    }
}
#endif
