
#include <QtCore/qobject.h>
#include <QUrl>
#include <QMap>
#include "qwebkitglobal.h"
#include "qwebelement.h"

#include "instrumentation/executionlistener.h"

#include "../JavaScriptCore/instrumentation/jscexecutionlistener.h"

#ifndef QWEBEXECUTIONLISTENER_H
#define QWEBEXECUTIONLISTENER_H

namespace JSC {
    class ExecState;
}

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
    virtual void javascript_bytecode_executed(JSC::Interpreter* interpreter, JSC::CodeBlock*, JSC::Instruction* inst); // interpreter instrumentation
    virtual void javascript_property_read(std::string propertyName, JSC::ExecState*);
    virtual void javascript_property_written(std::string propertyName, JSC::ExecState*);

    virtual void javascript_constant_encountered(std::string constant);
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

    static QWebExecutionListener* getListener();
    static void attachListeners();

private:
    QMap<int, WebCore::ScriptExecutionContext*> m_timers;

    QMap<int, WebCore::LazyXMLHttpRequest*> m_ajax_callbacks;
    int m_ajax_callback_next_id;

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

    void sigJavascriptConstantEncountered(QString constant);

    void sigJavascriptPropertyRead(QString propertyName, intptr_t codeBlockID, intptr_t SourceID, QUrl url, int startline);
    void sigJavascriptPropertyWritten(QString propertyName, intptr_t codeBlockID, intptr_t SourceID, QUrl url, int startline);

    void loadedJavaScript(QString source, QUrl url, uint startline);
    void statementExecuted(uint linenumber, QUrl url, uint startline);

    void sigJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint sourceOffset, QUrl url, uint startline, uint functionLine);
    void sigJavascriptFunctionReturned(QString functionName);
    void sigJavascriptBytecodeExecuted(QString opcode, uint bytecodeOffset, uint sourceOffset, QUrl url, uint startline);

};



#endif // QWEBEXECUTIONLISTENER_H

