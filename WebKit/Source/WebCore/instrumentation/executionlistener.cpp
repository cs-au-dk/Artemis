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
