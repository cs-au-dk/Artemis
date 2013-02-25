
#include <config.h>
#include <DOMWindow.h>
#include <QString>
#include <iostream>
#include "wtf/text/CString.h"

#include "JavaScriptCore/debugger/DebuggerCallFrame.h"
#include "JavaScriptCore/interpreter/Register.h"
#include "JavaScriptCore/runtime/JSObject.h"
#include "JavaScriptCore/runtime/JSValue.h"
#include "JavaScriptCore/runtime/Identifier.h"
#include "JavaScriptCore/heap/Heap.h"
#include "WebCore/xml/XMLHttpRequest.h"
#include "WebCore/xml/LazyXMLHttpRequest.h"
#include "WebCore/dom/ScriptExecutionContext.h"
#include "WebCore/page/DOMTimer.h"
#include "JavaScriptCore/parser/SourceCode.h"
#include "JavaScriptCore/interpreter/CallFrame.h"
#include "JavaScriptCore/runtime/ScopeChain.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"

#include "qwebexecutionlistener.h"

using namespace std;

QWebExecutionListener::QWebExecutionListener(QObject *parent) : QObject(parent), inst::ExecutionListener(), jscinst::JSCExecutionListener()
{
}

void QWebExecutionListener::eventAdded(WebCore::EventTarget * target, const char* type) {
    std::string typeString = std::string(type);

    if (target->toNode() != NULL) {
        emit addedEventListener(new QWebElement(target->toNode()), QString(tr(typeString.c_str())));

    } else if (target->toDOMWindow() != NULL) {
        emit addedEventListener(new QWebElement(target->toDOMWindow()->frameElement()), QString(tr(typeString.c_str())));

    } else if (typeString.compare("readystatechange") == 0) {
        std::cout << "WEBKIT::AJAX CALLBACK DETECTED (and ignored in event added)" << std::endl;

    } else {
        std::cout << "ERROR: Strange event: " << typeString << std::endl;
    }

    return;
}

void QWebExecutionListener::eventCleared(WebCore::EventTarget * target, const char* type) {
    std::string typeString = std::string(type);

    if (target->toNode() != NULL) {
        emit removedEventListener(new QWebElement(target->toNode()), QString(tr(typeString.c_str())));

     } else if (target->toDOMWindow() != NULL) {
        emit removedEventListener(new QWebElement(target->toDOMWindow()->frameElement()), QString(tr(typeString.c_str())));

    } else {
        std::cout << "ERROR: Strange event cleared:" << typeString << std::endl;
    }

    return;
}

void QWebExecutionListener::ajaxCallbackEventAdded(WebCore::LazyXMLHttpRequest* xmlHttpRequest) {
    int id = m_ajax_callbacks.size();
    m_ajax_callbacks.insert(id, xmlHttpRequest);
    emit addedAjaxCallbackHandler(id);
}

void QWebExecutionListener::ajaxCallbackFire(int callbackId) {
	WebCore::LazyXMLHttpRequest* xmlHttpRequest = m_ajax_callbacks.value(callbackId);
	xmlHttpRequest->fire();
	delete xmlHttpRequest;

	m_ajax_callbacks.remove(callbackId);
}

void QWebExecutionListener::clearAjaxCallbacks() {
	m_ajax_callbacks.clear();
}

// TIMERS START

void QWebExecutionListener::timerAdded(WebCore::ScriptExecutionContext* context, int timerId, int timeout, bool singleShot) {
    m_timers.insert(timerId, context);
    emit addedTimer(timerId, timeout, singleShot);
}
    
void QWebExecutionListener::timerRemoved(WebCore::ScriptExecutionContext* context, int timerId) {
    m_timers.remove(timerId);
    emit removedTimer(timerId);
}

void QWebExecutionListener::timerFire(int timerId) {
    Q_ASSERT(timerId > 0);

    QMap<int, WebCore::ScriptExecutionContext*>::const_iterator i = m_timers.find(timerId);
    
    if (i != m_timers.constEnd() && i.key() == timerId) {
        i.value()->findTimeout(timerId)->fired();
    }

    i++;
    Q_ASSERT(i != m_timers.constEnd());
}

void QWebExecutionListener::clearTimers() {
    m_timers.clear();
}

// TIMERS END

void QWebExecutionListener::javascript_code_loaded(JSC::SourceProvider* sp, JSC::ExecState*) {
    // SourceProvider has changed API lately, thus the following usage of it has not been fully
    // tested with artemis - e.g. if you are tracking an error and reach this point, then you
    // have come to the right place.

    std::string source(sp->getRange(0, sp->length()).utf8().data());
    std::string url(sp->url().utf8().data());
    intptr_t id = sp->asID();
    int startline = sp->startPosition().m_line.zeroBasedInt() + 1; // startPosition is placed right before the first line, thus (+1)

    emit loadedJavaScript(id, QString(tr(source.c_str())), QUrl(QString(tr(url.c_str()))), startline);
}

void QWebExecutionListener::javascript_executed_statement(const JSC::DebuggerCallFrame&, intptr_t sourceID, int linenumber) {
    /* std::string(frame.calculatedFunctionName().ascii().data()) */
    emit statementExecuted(sourceID, "fakeFunktionName()", linenumber);
}

bool domNodeSignature(JSC::CallFrame * cframe, JSC::JSObject * domElement, QString * signature) {
    
    JSC::Identifier nodeNameIdent(cframe, "nodeName");
    JSC::Identifier parentNodeIdent(cframe, "parentNode");

    if (domElement->hasProperty(cframe, nodeNameIdent) == false ||
        domElement->hasProperty(cframe, parentNodeIdent) == false)

        {
            cout << "Encountered dom-node missing either nodeName or parentNode" << endl;
            return false;
        }

    JSC::JSValue nodeName = domElement->get(cframe, nodeNameIdent);
    JSC::JSValue parentNode = domElement->get(cframe, parentNodeIdent);

    if (nodeName.isString() == false) {
        cout << "Encountered dom-node with non-string nodeName" << endl;
        return false;
    }

    *signature = signature->prepend(QObject::tr("."));
    *signature = signature->prepend(QString(QObject::tr(nodeName.getString(cframe).ascii().data())));

    if (parentNode.isObject() == false) {
        /* This must be the last node */
        return true;
    }

    JSC::JSObject * parentNodeObj = parentNode.getObject();

    return domNodeSignature(cframe, parentNodeObj, signature);

}

/**
    Try to detect and track calls to the jQuery.event.add
    method, such that we can select better targets for our
    events. 

    Currently, the following must be inserted in one of the
    loaded script files BEFORE! any events are added in 
    jQuery. 

    // INSTRUMENTATION 
    old_event_add = jQuery.event.add
   
    function __jquery_event_add__(elem, types, handler, data, selector) {
        return old_event_add(elem, types, handler, data, selector);
    }

    jQuery.event.add = __jquery_event_add__
    // INSTRUMENTATION END

    This should be replaced by a better solution at some point.
**/
void QWebExecutionListener::calledFunction(const JSC::DebuggerCallFrame& frame) {

    std::string functionName = std::string(frame.calculatedFunctionName().ascii().data());

    emit sigJavascriptFunctionCalled(QString::fromStdString(functionName), (intptr_t)frame.callFrame()->codeBlock(), frame.callFrame()->codeBlock()->numberOfInstructions());

    if (functionName.compare("__jquery_event_add__") == 0) {

        JSC::CallFrame* cframe = frame.callFrame();
        JSC::JSValue element = cframe->argument(0);
        
        if (element.isObject() == false) {
            cout << "WARNING: unknown element encountered when handling JQuery support" << endl;
            return;

        }

        QString signature(tr(""));
        domNodeSignature(cframe, element.getObject(), &signature);

        JSC::JSValue event = cframe->argument(1);
        
        if (event.isString() == false) {
            cout << "WARNING: unknown event encountered when handling JQuery support" << endl;
            return;
        }

        JSC::JSValue selector = cframe->argument(4);

        if (selector.isString() == false) {
            // This is not really fatal, in some cases an undefined
            // or null selector is given (presumably when doing a 
            // direct bind)
            cout << "WARNING: unknown selector encountered when handling JQuery support" << endl;
            return;
        }

        /* JQuery SUPPORT */
        emit jqueryEventAdded(signature,
                              QString(tr(event.getString(cframe).ascii().data())),
                              QString(tr(selector.getString(cframe).ascii().data())));
    }
}

void QWebExecutionListener::exceptional_condition(std::string cause, intptr_t sourceID, int lineNumber) {
    emit script_crash(QString(tr(cause.c_str())), sourceID, lineNumber);
}

void QWebExecutionListener::script_changed_url(std::string url) {
    QString urlString = tr(url.c_str());
    QUrl qurl = QUrl(urlString);
    emit script_url_load(qurl);
}


void QWebExecutionListener::webkit_ajax_send(const char * url, const char * data) {
    QUrl url_u = QUrl(QString(tr(url)));
    QString data_q = data == 0 ? QString(tr("")) : QString(tr(data));
    emit ajax_request(url_u, data_q);
}

void QWebExecutionListener::javascript_constant_encountered(std::string constant) {
    emit sigJavascriptConstantEncountered(QString::fromStdString(constant));
}

void QWebExecutionListener::javascript_eval_call(const char * eval_string) {
    Q_CHECK_PTR(eval_string);
    emit this->eval_call(QString(tr(eval_string)));
}

void QWebExecutionListener::javascript_bytecode_executed(JSC::CodeBlock* codeBlock, JSC::Instruction* instuction) {

    size_t bytecodeOffset = instuction - codeBlock->instructions().begin();

    emit sigJavascriptBytecodeExecuted((intptr_t)codeBlock, bytecodeOffset);

    /*jsc_bytecode_executed(codeBlock->source()->url().utf8(false).data(),
                          codeBlock->lineNumberForBytecodeOffset(offset),
                          offset,
                          -1); //TODO: Find out how to get the opcode from WebKit */
}

QWebExecutionListener* QWebExecutionListener::getListener() {
    return (QWebExecutionListener*)inst::getListener();
}

void QWebExecutionListener::attachListeners() {
    jscinst::register_jsc_listener(QWebExecutionListener::getListener());
}

namespace inst {

ExecutionListener* listener = 0;

ExecutionListener* getListener() {
    if (listener == NULL) {
        listener = new QWebExecutionListener();
    }
    return listener;
}

}

