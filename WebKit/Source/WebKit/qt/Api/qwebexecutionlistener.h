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

#include <QtCore/qobject.h>
#include <QUrl>
#include <QMap>
#include "qwebkitglobal.h"
#include "qwebelement.h"

#include "instrumentation/executionlistener.h"

#include "../JavaScriptCore/instrumentation/jscexecutionlistener.h"
#include "../JavaScriptCore/instrumentation/bytecodeinfo.h"
#include "../JavaScriptCore/symbolic/pathcondition.h"

#include "artemis/qsource.h"
#include "artemis/qsourceregistry.h"

#ifndef QWEBEXECUTIONLISTENER_H
#define QWEBEXECUTIONLISTENER_H

namespace JSC {
    class ExecState;
}

struct ByteCodeInfoStruct
{
    unsigned int linenumber;
    unsigned int bytecodeOffset;
    int divot;
    int startOffset;
    int endOffset;
    bool isSymbolic;
};

Q_DECLARE_METATYPE(ByteCodeInfoStruct);

class QWEBKIT_EXPORT QWebExecutionListener : public QObject, public inst::ExecutionListener, public jscinst::JSCExecutionListener
{
    Q_OBJECT

public:
    explicit QWebExecutionListener(QObject *parent = 0);

    virtual void eventAdded(WebCore::EventTarget * target, const char* type);
    virtual void eventCleared(WebCore::EventTarget * target, const char* type);
    virtual void eventTriggered(WebCore::EventTarget * target, const char* type);

    virtual void javascript_code_loaded(JSC::SourceProvider* sp, JSC::ExecState*);
    virtual void exceptional_condition(std::string cause, intptr_t sourceID, int lineNumber);
    virtual void url_changed(JSC::JSValue, JSC::ExecState* e);
    virtual void webkit_ajax_send(const char * url, const char * data);
    virtual void javascript_called_function(const JSC::DebuggerCallFrame&);
    virtual void javascript_returned_function(const JSC::DebuggerCallFrame&);

    virtual void javascript_executed_statement(const JSC::DebuggerCallFrame&, uint lineNumber); // from the debugger
    virtual void javascript_bytecode_executed(JSC::Interpreter* interpreter, JSC::CodeBlock*, JSC::Instruction* inst, const JSC::BytecodeInfo& info); // interpreter instrumentation
    virtual void javascript_property_read(std::string propertyName, JSC::ExecState*);
    virtual void javascript_property_written(std::string propertyName, JSC::ExecState*);

    void javascriptConstantStringEncountered(std::string constant);
    virtual void webkit_eval_call(const char * eval_string);

    virtual void ajaxCallbackEventAdded(WebCore::LazyXMLHttpRequest*);

    void ajaxCallbackFire(int callbackId);
    void clearAjaxCallbacks();

    virtual void timerAdded(WebCore::ScriptExecutionContext* context, int timerId, int timeout, bool singleShot);
    virtual void timerRemoved(WebCore::ScriptExecutionContext* context, int timerId);
    void timerFire(int timerId);
    void clearTimers();

    void beginSymbolicSession();
    void endSymbolicSession();
    Symbolic::PathCondition* getLastPathCondition();
    QString generatePathConditionString();


    static QWebExecutionListener* getListener();
    static void attachListeners();

private:
    QMap<int, WebCore::ScriptExecutionContext*> m_timers;

    QMap<int, WebCore::LazyXMLHttpRequest*> m_ajax_callbacks;
    int m_ajax_callback_next_id;

    QSourceRegistry m_sourceRegistry;

signals:
    void addedEventListener(QWebElement*, QString);
    void removedEventListener(QWebElement*, QString);
    void triggeredEventListener(QWebElement*, QString);
    
    void addedAjaxCallbackHandler(int callbackId);

    void addedTimer(int timerId, int timeout, bool singleShot);
    void removedTimer(int timerId);

    void script_crash(QString cause, intptr_t sourceID, int lineNumber);
    void script_url_load(QUrl url);
    void ajax_request(QUrl, QString post_data);  
    void eval_call(QString source_text);

    void jqueryEventAdded(QString elementSignature, QString event, QString selectors); 

    /* Constant String Instrumentation */
    void sigJavascriptConstantStringEncountered(QString constant);

    /* Property Access Instrumentation */
    void sigJavascriptPropertyRead(QString propertyName, intptr_t codeBlockID, intptr_t SourceID, QSource* source);
    void sigJavascriptPropertyWritten(QString propertyName, intptr_t codeBlockID, intptr_t SourceID, QSource* source);

    void loadedJavaScript(QString sourcecode, QSource* source);
    void statementExecuted(uint linenumber, QSource* source);
    void sigJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint functionLine, uint sourceOffset, QSource* source);
    void sigJavascriptFunctionReturned(QString functionName);
    void sigJavascriptBytecodeExecuted(QString opcode, uint sourceOffset, QSource* source, const ByteCodeInfoStruct byteInfo);

};



#endif // QWEBEXECUTIONLISTENER_H

