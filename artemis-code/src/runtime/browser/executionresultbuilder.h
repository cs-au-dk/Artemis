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
#ifndef EXECUTIONRESULTBUILDER_H
#define EXECUTIONRESULTBUILDER_H

#include <QObject>
#include <QSharedPointer>
#include <QWebElement>
#include <QPair>
#include <QList>
#include <QString>

#include "runtime/browser/executionresult.h"
#include "runtime/browser/artemiswebpage.h"

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
    explicit ExecutionResultBuilder(ArtemisWebPagePtr page);
    
    void reset();
    void notifyPageLoaded();
    void notifyStartingEvent();
    void notifyStartingLoad();
    QSharedPointer<ExecutionResult> getResult();

private:
    void registerFromFieldsIntoResult();
    void registerEventHandlersIntoResult();

    QSet<QString> getSelectOptions(const QWebElement&);
    QSet<QWebFrame*> getAllFrames();

    QSharedPointer<ExecutionResult> mResult;
    ArtemisWebPagePtr mPage;
    QString mPageStateAfterLoad;

    QList<QPair<QWebElement*, QString> > mElementPointers;

public slots:
    void slScriptCrashed(QString cause, intptr_t sourceID, int lineNumber);
    void slStringEvaled(const QString);

    void slTimerAdded(int timerId, int timeout, bool singleShot);
    void slTimerRemoved(int timerId);

    void slEventListenerAdded(QWebElement* elem, QString name);
    void slEventListenerRemoved(QWebElement* elem, QString name);

    void slAjaxCallbackHandlerAdded(int callbackId);
    void slAjaxRequestInitiated(QUrl, QString postData);

    void slJavascriptConstantEncountered(QString constant);

};

typedef QSharedPointer<ExecutionResultBuilder> ExecutionResultBuilderPtr;
typedef QSharedPointer<const ExecutionResultBuilder> ExecutionResultBuilderConstPtr;

}

#endif // EXECUTIONRESULTBUILDER_H
