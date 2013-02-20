#ifndef EXECUTIONRESULTBUILDER_H
#define EXECUTIONRESULTBUILDER_H

#include <QObject>
#include <QSharedPointer>
#include <QWebPage>
#include <QWebElement>
#include <QPair>
#include <QString>

#include "runtime/browser/executionresult.h"

namespace artemis
{

/**
 * @brief The ExecutionResultBuilder class
 *
 * The ExecutionResultBuilder is tasked with constructing a ExecutionResult object
 * based on a concrete execution of a configuration.
 *
 * Notice, that this class has access to execution time information (the web page
 * and the DOM model) that the ExecutionResult object can't contain - since it is
 * retained long after the web page have been deallocated.
 *
 * Notice, that signals will be sent from the webpage after getResult and before
 * reset is called! E.g. if a webpage is deallocated then we will receive "event
 * handler removed" events.
 */
class ExecutionResultBuilder : public QObject
{
    Q_OBJECT

public:
    explicit ExecutionResultBuilder(QObject *parent, QWebPage* page);
    
    void reset();
    void notifyPageLoaded();
    QSharedPointer<ExecutionResult> getResult();

private:
    void registerFromFieldsIntoResult();
    void registerEventHandlersIntoResult();

    QSet<QString> getSelectOptions(const QWebElement&);
    QSet<QWebFrame*> getAllFrames();

    QSharedPointer<ExecutionResult> mResult;
    QWebPage* mPage;
    QString mPageStateAfterLoad;

    QSet<QPair<QWebElement*, QString> > mElementPointers;

public slots:
    void slScriptCrashed(QString cause, intptr_t sourceID, int lineNumber);
    void slStringEvaled(const QString);
    void slCodeLoaded(intptr_t, QString, QUrl, int);

    void slTimerAdded(int timerId, int timeout, bool singleShot);
    void slTimerRemoved(int timerId);

    void slEventListenerAdded(QWebElement* elem, QString name);
    void slEventListenerRemoved(QWebElement* elem, QString name);

    void slAjaxCallbackHandlerAdded(int callbackId);
    void slAjaxRequestInitiated(QUrl, QString postData);

    void slJavascriptConstantEncountered(QString constant);

};

}

#endif // EXECUTIONRESULTBUILDER_H
