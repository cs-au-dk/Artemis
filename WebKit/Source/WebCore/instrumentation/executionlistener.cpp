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
#include "WebCore/instrumentation/listenerdebugger.h"
#include "JavaScriptCore/runtime/Identifier.h"
#include "JavaScriptCore/runtime/ScopeChain.h"
#include "JavaScriptCore/interpreter/Register.h"
#include "WebCore/xml/XMLHttpRequest.h"
#include "WebCore/dom/ScriptExecutionContext.h"

#include "executionlistener.h"

namespace inst {

    ExecutionListener::ExecutionListener()
    {
    }

    void ExecutionListener::timerAdded(WebCore::ScriptExecutionContext* context, int timerId, int timeout, bool singleShot) {
        return;
    }
        
    void ExecutionListener::timerRemoved(WebCore::ScriptExecutionContext* context, int timerId) {
        return;
    }

    void ExecutionListener::ajaxCallbackEventAdded(WebCore::LazyXMLHttpRequest*) {
        return;
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
        //std::cout << "el::executed statement" << std::endl;
        /* std::string(frame.calculatedFunctionName().ascii().data()) */
        /* FIXME IMPORTANT */
        executedStatement(sourceID, "fooBar()", lineNumber);
    }

    void ExecutionListener::executedStatement(intptr_t sourceID, std::string function_name, int linenumber) {
        std::cout << "el::WARNING-EXE-STATEMENT-LOST" << std::endl;
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
