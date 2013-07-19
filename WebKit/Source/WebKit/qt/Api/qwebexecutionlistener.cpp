/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <QDebug>
#include <config.h>
#include <DOMWindow.h>
#include <QString>
#include <QDebug>
#include <QDateTime>
#include <QFile>
#include <QTextStream>
#include <iostream>
#include "wtf/text/CString.h"

#include "JavaScriptCore/runtime/UString.h"

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
#include "JavaScriptCore/bytecode/Opcode.h"
#include "JavaScriptCore/interpreter/Interpreter.h"

#include "qwebexecutionlistener.h"

using namespace std;

QWebExecutionListener::QWebExecutionListener(QObject *parent) :
    QObject(parent),
    inst::ExecutionListener(),
    jscinst::JSCExecutionListener(),
    m_ajax_callback_next_id(0),
    m_reportHeapMode(0)
{
}

void QWebExecutionListener::eventAdded(WebCore::EventTarget * target, const char* type) {
    std::string typeString = std::string(type);

    if (target->toNode() != NULL) {
        emit addedEventListener(new QWebElement(target->toNode()), QString(tr(typeString.c_str())));

    } else if (target->toDOMWindow() != NULL) {
        emit addedEventListener(new QWebElement(target->toDOMWindow()->frameElement()), QString(tr(typeString.c_str())));

    } else if (typeString.compare("readystatechange") == 0) {
        qDebug() << QString::fromStdString("WEBKIT::AJAX CALLBACK DETECTED (and ignored in event added)");

    } else {
        qWarning() << QString::fromStdString("Strange event: ") << QString::fromStdString(typeString);
    }

    return;
}

void QWebExecutionListener::enableHeapReport(bool namedOnly, int heapReportNumber){
    m_reportHeapMode = namedOnly?1:2;
    qDebug() << "SETTING HEAPN" << heapReportNumber;
    m_heapReportNumber = heapReportNumber;
}

QList<QString> QWebExecutionListener::getHeapReport(int &heapReportNumber){
    heapReportNumber = m_heapReportNumber;
    return m_heapReport;
}

void QWebExecutionListener::eventCleared(WebCore::EventTarget * target, const char* type) {
    std::string typeString = std::string(type);

    if (target->toNode() != NULL) {
        emit removedEventListener(new QWebElement(target->toNode()), QString(tr(typeString.c_str())));

     } else if (target->toDOMWindow() != NULL) {
        emit removedEventListener(new QWebElement(target->toDOMWindow()->frameElement()), QString(tr(typeString.c_str())));

    } else {
        qWarning() << QString::fromStdString("Strange event cleared: ") << QString::fromStdString(typeString);
    }

    return;
}

void QWebExecutionListener::eventTriggered(WebCore::EventTarget * target, const char* type) {
    std::string typeString = std::string(type);

    if (target->toNode() != NULL) {
        emit triggeredEventListener(new QWebElement(target->toNode()), QString(tr(typeString.c_str())));

     } else if (target->toDOMWindow() != NULL) {
        emit triggeredEventListener(new QWebElement(target->toDOMWindow()->frameElement()), QString(tr(typeString.c_str())));

    } else {
        qWarning() << QString::fromStdString("Strange event triggered: ") << QString::fromStdString(typeString);
    }

    return;
}

// AJAX SUPPORT

void QWebExecutionListener::ajaxCallbackEventAdded(WebCore::LazyXMLHttpRequest* xmlHttpRequest) {
    int callbackId = m_ajax_callback_next_id;
    m_ajax_callback_next_id++;

    m_ajax_callbacks.insert(callbackId, xmlHttpRequest);
    emit addedAjaxCallbackHandler(callbackId);
}

void QWebExecutionListener::ajaxCallbackFire(int callbackId) {
    WebCore::LazyXMLHttpRequest* xmlHttpRequest = m_ajax_callbacks.value(callbackId);

	xmlHttpRequest->fire();

    m_ajax_callbacks.remove(callbackId);
	delete xmlHttpRequest;
}

void QWebExecutionListener::clearAjaxCallbacks() {
    m_ajax_callbacks.clear();
    m_ajax_callback_next_id = 0;
}

void QWebExecutionListener::webkit_ajax_send(const char * url, const char * data) {
    QUrl url_u = QUrl(QString(tr(url)));
    QString data_q = data == 0 ? QString(tr("")) : QString(tr(data));
    emit ajax_request(url_u, data_q);
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


void QWebExecutionListener::javascript_called_function(const JSC::DebuggerCallFrame& frame) {

    std::string functionName = std::string(frame.calculatedFunctionName().ascii().data());
    JSC::CodeBlock* codeBlock = frame.callFrame()->codeBlock();

    if(m_reportHeapMode > 0 && (m_reportHeapMode > 1 || functionName.length() > 0)){


        JSC::JSObject* functionObject = frame.callFrame()->callee();
        std::stringstream ss;
        ss << std::string(JSC::JSObject::className(functionObject).ascii().data()) ;
        ss << "@";
        ss << (const void *) static_cast<const void*>(functionObject);
        QString url = m_sourceRegistry.get(frame.callFrame()->codeBlock()->source())->getUrl();
        string fn = functionName.length() >0 ? "\""+functionName + "\"" : "null";

        string offset = QString::number(((JSC::JSFunction*) functionObject)->sourceCode()->startOffset()).toStdString();
        string s = "{\"function-name\":"+fn+", \"object-name\": \""+ss.str()+"\", \"source\":\""+url.toStdString()+"\", \"line-number\":";
        QString dt = QDateTime::currentDateTime().toString(QString::fromStdString("dd-MM-yy-hh-mm-ss"));
        QString hReport = QString::fromStdString(s)
                .append(QString::number(codeBlock->lineNumberForBytecodeOffset(0)))
                .append(QString::fromStdString(", \"char-offset\":"+offset+", "))
                .append(QString::fromStdString("\"time\":\""))
                .append(dt)
                .append(QString::fromStdString("\", \"state\":"));
        frame.callFrame()->heap()->heapAsString(frame.callFrame(), &hReport);
        hReport.append(QString::fromStdString("}"));
        m_heapReport.append(hReport);

        if(m_heapReport.length() >=100){
            QString buffer;
            int i = 0 ;
            foreach(QString rap, m_heapReport){
                buffer += rap;
                if (i < m_heapReport.length()-1){
                    buffer += QString::fromStdString(", ");
                }
                i++;
            }
            QString numberStr = QString::number(m_heapReportNumber);
            buffer = QString::fromStdString("{\"heap-report\":[").append(buffer).append(QString::fromStdString("]}"));
            QFile file(QString::fromStdString("heap-report-") + QDateTime::currentDateTime().toString(QString::fromStdString("dd-MM-yy-hh-mm-ss"))+QString::fromStdString(" (")+numberStr+QString::fromStdString(").json"));
            file.open(QIODevice::WriteOnly | QIODevice::Text);
            QTextStream out(&file);
            out << (buffer.isEmpty() ? QString::fromStdString(" ") : buffer);
            file.close();
            out.flush();
            m_heapReportNumber++;
            m_heapReport.clear();

        }


    }


    emit sigJavascriptFunctionCalled(QString::fromStdString(functionName),
                                     codeBlock->numberOfInstructions(),
                                     codeBlock->lineNumberForBytecodeOffset(0),
                                     codeBlock->sourceOffset(),
                                     m_sourceRegistry.get(codeBlock->source()));

    if (functionName.compare("__jquery_event_add__") == 0) {

        JSC::CallFrame* cframe = frame.callFrame(); JSC::JSValue element = cframe->argument(0);
        
        if (element.isObject() == false) {
            qWarning() << "WARNING: unknown element encountered when handling JQuery support";
            return;

        }

        QString signature(tr(""));
        domNodeSignature(cframe, element.getObject(), &signature);

        JSC::JSValue event = cframe->argument(1);
        
        if (event.isString() == false) {
            qWarning() << "WARNING: unknown event encountered when handling JQuery support";
            return;
        }

        JSC::JSValue selector = cframe->argument(4);

        if (selector.isString() == false) {
            // This is not really fatal, in some cases an undefined
            // or null selector is given (presumably when doing a 
            // direct bind)
            qWarning() << "WARNING: unknown selector encountered when handling JQuery support";
            return;
        }

        /* JQuery SUPPORT */
        emit jqueryEventAdded(signature,
                              QString(tr(event.getString(cframe).ascii().data())),
                              QString(tr(selector.getString(cframe).ascii().data())));
    }
}

void QWebExecutionListener::javascript_returned_function(const JSC::DebuggerCallFrame& frame) {

    std::string functionName = std::string(frame.calculatedFunctionName().ascii().data());

    emit sigJavascriptFunctionReturned(QString::fromStdString(functionName));
}

void QWebExecutionListener::exceptional_condition(std::string cause, intptr_t sourceID, int lineNumber) {
    emit script_crash(QString(tr(cause.c_str())), sourceID, lineNumber);
}

void QWebExecutionListener::url_changed(JSC::JSValue value, JSC::ExecState* e) {
    std::string url;

    if (value.isString()) {
        url = std::string(value.getString(e).utf8().data());
    } else {
        url = std::string(value.toString(e).utf8().data());
    }

    QUrl qurl = QUrl(tr(url.c_str()));
    emit script_url_load(qurl);
}

/* Constant String Instrumentation */

void QWebExecutionListener::javascriptConstantStringEncountered(std::string constant)
{
    emit sigJavascriptConstantStringEncountered(QString::fromStdString(constant));
}

void QWebExecutionListener::webkit_eval_call(const char * eval_string) {
    Q_CHECK_PTR(eval_string);
    emit this->eval_call(QString(tr(eval_string)));
}

void QWebExecutionListener::javascript_code_loaded(JSC::SourceProvider* sp, JSC::ExecState*) {
    // SourceProvider has changed API lately, thus the following usage of it has not been fully
    // tested with artemis - e.g. if you are tracking an error and reach this point, then you
    // have come to the right place.

    std::string source(sp->getRange(0, sp->length()).utf8().data());

    emit loadedJavaScript(QString(tr(source.c_str())), m_sourceRegistry.get(sp));
}

void QWebExecutionListener::javascript_executed_statement(const JSC::DebuggerCallFrame& callFrame, uint linenumber) {
    JSC::SourceProvider* sourceProvider = callFrame.callFrame()->codeBlock()->source();

    emit statementExecuted(linenumber,
                           m_sourceRegistry.get(sourceProvider));
}

void QWebExecutionListener::javascript_bytecode_executed(JSC::Interpreter* interpreter, JSC::CodeBlock* codeBlock, JSC::Instruction* instruction, const JSC::BytecodeInfo& info) {

    uint bytecodeOffset = instruction - codeBlock->instructions().begin();

    ByteCodeInfoStruct binfo;
    codeBlock->expressionRangeForBytecodeOffset(bytecodeOffset,binfo.divot,binfo.startOffset,binfo.endOffset);
    binfo.linenumber = codeBlock->lineNumberForBytecodeOffset(bytecodeOffset);
    binfo.isSymbolic = info.isSymbolic();
    binfo.bytecodeOffset = bytecodeOffset;

    emit sigJavascriptBytecodeExecuted(tr(JSC::opcodeNames[interpreter->getOpcodeID(instruction->u.opcode)]),
                                       codeBlock->sourceOffset(),
                                       m_sourceRegistry.get(codeBlock->source()),
                                       binfo);
}

void QWebExecutionListener::javascript_property_read(std::string propertyName, JSC::CallFrame* callFrame)
{
    emit sigJavascriptPropertyRead(QString::fromStdString(propertyName),
                                   (intptr_t)callFrame->codeBlock(),
                                   callFrame->codeBlock()->source()->asID(),
                                   m_sourceRegistry.get(callFrame->codeBlock()->source()));
}

void QWebExecutionListener::javascript_property_written(std::string propertyName, JSC::CallFrame* callFrame)
{
    emit sigJavascriptPropertyWritten(QString::fromStdString(propertyName),
                                      (intptr_t)callFrame->codeBlock(),
                                      callFrame->codeBlock()->source()->asID(),
                                      m_sourceRegistry.get(callFrame->codeBlock()->source()));
}

QWebExecutionListener* QWebExecutionListener::getListener() {
    return (QWebExecutionListener*)inst::getListener();
}

void QWebExecutionListener::attachListeners() {
    jscinst::register_jsc_listener(QWebExecutionListener::getListener());
}

/**
 * Marks the beginning of a symbolic session, right before events are triggered
 * but after the onload event has been handled.
 */
void QWebExecutionListener::beginSymbolicSession()
{
    JSC::Interpreter::m_symbolic->beginSession();
}

/**
 * Marks the end of a symbolic session, either after a series of events or when
 * the execution listener is detached. Is always called after a start session,
 * however no guarantee is made that it is not called more than once.
 */
void QWebExecutionListener::endSymbolicSession()
{
    JSC::Interpreter::m_symbolic->endSession();
}


QString QWebExecutionListener::generatePathConditionString(){
    return QString::fromStdString(JSC::Interpreter::m_symbolic->generatePathConditionString());
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

