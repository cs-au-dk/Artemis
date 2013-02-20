
#include <QtCore/qobject.h>
#include <QUrl>
#include <QMap>
#include "qwebkitglobal.h"
#include "qwebelement.h"

#include "instrumentation/executionlistener.h"

#include "../JavaScriptCore/instrumentation/jscexecutionlistener.h"

#ifndef QWEBEXECUTIONLISTENER_H
#define QWEBEXECUTIONLISTENER_H

class QWEBKIT_EXPORT QWebExecutionListener : public QObject, public inst::ExecutionListener, public jscinst::JSCExecutionListener
{
    Q_OBJECT

public:
    explicit QWebExecutionListener(QObject *parent = 0);

    virtual void eventAdded(WebCore::EventTarget * target, const char* type);
    virtual void eventCleared(WebCore::EventTarget * target, const char* type);

    virtual void scriptCodeLoaded(intptr_t id,std::string source, std::string url, int startline);
    virtual void executedStatement(intptr_t sourceID, std::string function_name, int linenumber);
    virtual void exceptional_condition(std::string cause, intptr_t sourceID, int lineNumber);
    virtual void script_changed_url( std::string url);
    virtual void webkit_ajax_send(const char * url, const char * data);
    virtual void calledFunction(const JSC::DebuggerCallFrame&);

    virtual void javascript_constant_encountered(std::string constant);
    virtual void javascript_eval_call(const char * eval_string);
    virtual void javascript_bytecode_executed(JSC::CodeBlock*, JSC::Instruction* inst);

    virtual void ajaxCallbackEventAdded(WebCore::LazyXMLHttpRequest*);

    void ajaxCallbackFire(int callbackId);
    void clearAjaxCallbacks();

    virtual void timerAdded(WebCore::ScriptExecutionContext* context, int timerId, int timeout, bool singleShot);
    virtual void timerRemoved(WebCore::ScriptExecutionContext* context, int timerId);
    void timerFire(int timerId);
    void clearTimers();

    static QWebExecutionListener* getListener();
    static void attachListeners();

private:
    QMap<int, WebCore::ScriptExecutionContext*> m_timers;
    QMap<int, WebCore::LazyXMLHttpRequest*> m_ajax_callbacks;

signals:
    void addedEventListener(QWebElement*, QString);
    void removedEventListener(QWebElement*, QString);
    
    void addedAjaxCallbackHandler(int callbackId);

    void addedTimer(int timerId, int timeout, bool singleShot);
    void removedTimer(int timerId);

    void loadedJavaScript(intptr_t id, QString source, QUrl url, int startline);
    void statementExecuted(intptr_t sourceID, std::string function_name, int linenumber);
    void script_crash(QString cause, intptr_t sourceID, int lineNumber);
    void script_url_load(QUrl url);
    void ajax_request(QUrl, QString post_data);  
    void eval_call(QString source_text);

    void jqueryEventAdded(QString elementSignature, QString event, QString selectors); 

    void sigJavascriptConstantEncountered(QString constant);

};



#endif // QWEBEXECUTIONLISTENER_H

