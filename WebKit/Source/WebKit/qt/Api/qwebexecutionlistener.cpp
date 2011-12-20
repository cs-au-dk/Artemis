
#include <config.h>
#include "qwebexecutionlistener.h"
#include <DOMWindow.h>
#include <QUrl>
#include <QString>

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

void QWebExecutionListener::nodeEventCleared(WebCore::Node *, const std::string) {
    //TODO
}

void QWebExecutionListener::domWindowEventCleared(WebCore::DOMWindow *, const std::string) {
    //TODO
}

void QWebExecutionListener::scriptCodeLoaded(intptr_t id,std::string source, std::string url ,int startline) {
    emit loadedJavaScript(id,QString(tr(source.c_str())), QUrl(QString(tr(url.c_str()))), startline);
}

void QWebExecutionListener::executedStatement(intptr_t sourceID, std::string function_name, int linenumber) {
    emit statementExecuted(sourceID,function_name,linenumber);
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

