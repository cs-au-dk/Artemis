
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
#include "WebCore/dom/ScriptExecutionContext.h"
#include "WebCore/page/DOMTimer.h"

#include "qwebexecutionlistener.h"

using namespace std;

QWebExecutionListener::QWebExecutionListener(QObject *parent) :
    QObject(parent),
    inst::ExecutionListener()
{
}

void QWebExecutionListener::domWindowEventAdded(WebCore::DOMWindow* window, const std::string s) {
    emit addedEventListener(new QWebElement(window->frameElement()), QString(tr(s.c_str())));
}

void QWebExecutionListener::nodeEventAdded(WebCore::Node * node, const std::string s) {
    emit addedEventListener(new QWebElement(node), QString(tr(s.c_str())));
}

void QWebExecutionListener::ajaxCallbackEventAdded(WebCore::XMLHttpRequest* xhr) {
    QAjaxCallbackHandler* handler = new QAjaxCallbackHandler(xhr);
    emit addedAjaxCallbackHandler(handler);
}

void QWebExecutionListener::nodeEventCleared(WebCore::Node *, const std::string) {
    //TODO
}

void QWebExecutionListener::domWindowEventCleared(WebCore::DOMWindow *, const std::string) {
    //TODO
}

void QWebExecutionListener::timerAdded(WebCore::ScriptExecutionContext* context, int timerId, int timeout, bool singleShot) {
    cout << "WEBKIT::Timer " << timerId << " Added" << endl;

    m_timers.insert(timerId, context);
    emit addedTimer(timerId, timeout, singleShot);
}
    
void QWebExecutionListener::timerRemoved(WebCore::ScriptExecutionContext* context, int timerId) {
    cout << "WEBKIT::Timer " << timerId << " Removed" << endl;

    m_timers.remove(timerId);
    emit removedTimer(timerId);
}

void QWebExecutionListener::timerFire(int timerId) {
    if (timerId == 0) {

        foreach(timerId, m_timers.keys()) {
            timerFire(timerId);
        }

    } else {

        QMap<int, WebCore::ScriptExecutionContext*>::const_iterator i = m_timers.find(timerId);
        
        while (i != m_timers.end() && i.key() == timerId) {
            cout << "WEBKIT::Timer Clear Clear... Fire Event! tid: " << timerId << endl;
            i.value()->findTimeout(timerId)->fired();
            ++i;
        }

    }
}

void QWebExecutionListener::clearTimers() {
    cout << "WEBKIT::Timer clearing" << endl;
    m_timers.clear();
}

void QWebExecutionListener::scriptCodeLoaded(intptr_t id, std::string source, std::string url, int startline) {
    emit loadedJavaScript(id, QString(tr(source.c_str())), QUrl(QString(tr(url.c_str()))), startline);
}

void QWebExecutionListener::executedStatement(intptr_t sourceID, std::string function_name, int linenumber) {
    emit statementExecuted(sourceID, function_name, linenumber);
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

    JSC::CallFrame * cframe = frame.callFrame();

    std::string functionName = std::string(frame.calculatedFunctionName().ascii().data());

    if (functionName.compare("__jquery_event_add__") == 0) {
        cout << "JQUERY SPECIFIC ADDITION DETECTED" << endl;
    
        
        JSC::JSValue element = cframe->argument(0);
        
        if (element.isObject() == false) {
            cout << "JQUERY::Error unknown element" << endl;
            return;

        }

        QString signature(tr(""));
        domNodeSignature(cframe, element.getObject(), &signature);

        JSC::JSValue event = cframe->argument(1);
        
        if (event.isString() == false) {
            cout << "JQUERY::Error unknown event" << endl;
            return;
        }

        JSC::JSValue selector = cframe->argument(4);

        if (selector.isString() == false) {
            // This is not really fatal, in some cases an undefined
            // or null selector is given (presumably when doing a 
            // direct bind)
            cout << "JQUERY::Warning unknown selector" << endl;
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

void QWebExecutionListener::webkit_eval_call(const char * eval_string) {
    Q_CHECK_PTR(eval_string);
    emit this->eval_call(QString(tr(eval_string)));
}

void installWebKitExecutionListener(inst::ExecutionListener* e) {
    inst::setDefaultListener(e);
}

