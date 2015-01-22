/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
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

#include "../WTF/wtf/ExportMacros.h"
#include "../JavaScriptCore/instrumentation/jscexecutionlistener.h"
#include "../JavaScriptCore/instrumentation/bytecodeinfo.h"
#include "../JavaScriptCore/symbolic/expr.h"
#include "../JavaScriptCore/bytecode/Opcode.h"

#include "artemis/qsource.h"
#include "artemis/qsourceregistry.h"

#ifndef QWEBEXECUTIONLISTENER_H
#define QWEBEXECUTIONLISTENER_H

namespace JSC {
    class ExecState;
}

struct ByteCodeInfoStruct
{
    JSC::OpcodeID opcodeId;
    unsigned int linenumber;
    unsigned int bytecodeOffset;
    int divot;
    int startOffset;
    int endOffset;
    bool isSymbolic;

    QString getOpcodeName() const {
        return QString::fromStdString(JSC::opcodeNames[opcodeId]);
    }
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
    virtual void javascript_branch_executed(bool jump, Symbolic::Expression* condition, JSC::ExecState*, const JSC::Instruction*, const JSC::BytecodeInfo&);
    virtual void javascript_symbolic_field_read(std::string variable, bool isSymbolic);

    void javascriptConstantStringEncountered(std::string constant);
    virtual void javascript_eval_call(const char * eval_string);

    virtual void ajaxCallbackEventAdded(WebCore::LazyXMLHttpRequest*);

    void ajaxCallbackFire(int callbackId);
    void clearAjaxCallbacks();

    void page_load_scheduled(const char* url);

    virtual void timerAdded(WebCore::ScriptExecutionContext* context, int timerId, int timeout, bool singleShot);
    virtual void timerRemoved(WebCore::ScriptExecutionContext* context, int timerId);
    void timerFire(int timerId);
    void clearTimers();

    void enableHeapReport(bool namedOnly, int heapReportNumber, int factor);
    QList<QString> getHeapReport(int &heapReportNumber);

    void beginSymbolicSession();
    void endSymbolicSession();
    unsigned int getSymbolicSessionId();

    static QWebExecutionListener* getListener();
    static void attachListeners();

private:
    QMap<int, WebCore::ScriptExecutionContext*> m_timers;

    QMap<int, WebCore::LazyXMLHttpRequest*> m_ajax_callbacks;
    int m_ajax_callback_next_id;

    QSourceRegistry m_sourceRegistry;
    QList<QString> m_heapReport;
    int m_reportHeapMode;
    int m_heapReportNumber;
    int m_heapReportFactor;
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

    /* JavaScript Instrumentation */
    void loadedJavaScript(QString sourcecode, QSource* source);
    void statementExecuted(uint linenumber, QSource* source);
    void sigJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint functionLine, uint sourceOffset, QSource* source);
    void sigJavascriptFunctionReturned(QString functionName);
    void sigJavascriptBytecodeExecuted(const ByteCodeInfoStruct byteInfo, uint sourceOffset, QSource* source);
    void sigJavascriptBranchExecuted(bool jump, Symbolic::Expression* condition, uint sourceOffset, QSource* source, const ByteCodeInfoStruct byteInfo);
    void sigJavascriptSymbolicFieldRead(QString variable, bool isSymbolic);

    /* Page Load Instrumentation */
    void sigPageLoadScheduled(QUrl url);
};



#endif // QWEBEXECUTIONLISTENER_H

