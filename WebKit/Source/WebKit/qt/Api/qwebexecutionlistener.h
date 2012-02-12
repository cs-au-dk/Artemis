
#include <QtCore/qobject.h>
#include <QUrl>
#include "qwebkitglobal.h"
#include "qwebelement.h"

#include "instrumentation/executionlistener.h"

#ifndef QWEBEXECUTIONLISTENER_H
#define QWEBEXECUTIONLISTENER_H

class QWEBKIT_EXPORT QWebExecutionListener : public QObject, public inst::ExecutionListener
{
    Q_OBJECT
public:
    explicit QWebExecutionListener(QObject *parent = 0);

    //Overrides!
    virtual void domWindowEventAdded(WebCore::DOMWindow*, const std::string);
    virtual void nodeEventAdded( WebCore::Node*, const std::string);
    virtual void domWindowEventCleared(WebCore::DOMWindow*, const std::string);
    virtual void nodeEventCleared(WebCore::Node*, const std::string);
    virtual void scriptCodeLoaded(intptr_t id,std::string source, std::string url, int startline);
    virtual void executedStatement(intptr_t sourceID, std::string function_name, int linenumber);
    virtual void exceptional_condition(std::string cause, intptr_t sourceID, int lineNumber);
    virtual void script_changed_url( std::string url);
    virtual void webkit_ajax_send(const char * url, const char * data);
    virtual void webkit_eval_call(const char * eval_string);
    virtual void calledFunction(const JSC::DebuggerCallFrame&);

signals:
    void addedEventListener(QWebElement*, QString );
    void removedEventListener(QWebElement*, QString );
    void loadedJavaScript(intptr_t id,QString source, QUrl url, int startline);
    void statementExecuted(intptr_t sourceID, std::string function_name, int linenumber);
    void script_crash(QString cause, intptr_t sourceID, int lineNumber);
    void script_url_load(QUrl url);
    void ajax_request(QUrl, QString post_data);  
    void eval_call(QString source_text);

    void jqueryEventAdded(QString elementSignature, QString event, QString selectors); 

public slots:

};

void installWebKitExecutionListener(inst::ExecutionListener*);

#endif // QWEBEXECUTIONLISTENER_H

