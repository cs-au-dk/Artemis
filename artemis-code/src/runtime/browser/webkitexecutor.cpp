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

#include <iostream>
#include <unistd.h>

#include <QtWebKit>
#include <QSource>
#include <QApplication>
#include <QStack>
#include <QDebug>
#include <QWebExecutionListener>

#include "runtime/input/forms/formfield.h"
#include "runtime/input/events/domelementdescriptor.h"
#include "runtime/input/baseinput.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "util/loggingutil.h"
#include "concolic/executiontree/tracebuilder.h"

#include "webkitexecutor.h"

using namespace std;

namespace artemis
{

WebKitExecutor::WebKitExecutor(QObject* parent,
                               AppModelPtr appmodel,
                               QMap<QString, QString> presetFields,
                               JQueryListener* jqueryListener,
                               AjaxRequestListener* ajaxListener,
                               bool enableConstantStringInstrumentation) :
    QObject(parent),
    mNextOpCanceled(false), mKeepOpen(false)
{

    mPresetFields = presetFields;
    mJquery = jqueryListener;

    mAjaxListener = ajaxListener;
    mAjaxListener->setParent(this);

    mPage = ArtemisWebPagePtr(new ArtemisWebPage());
    mPage->setNetworkAccessManager(mAjaxListener);

    QObject::connect(mPage.data(), SIGNAL(loadFinished(bool)),
                     this, SLOT(slLoadFinished(bool)));
    QObject::connect(mPage.data()->networkAccessManager(), SIGNAL(finished(QNetworkReply*)), this, SLOT(slNAMFinished(QNetworkReply*)));
    QObject::connect(mPage.data(), SIGNAL(loadProgress(int)),
                     this, SLOT(slLoadProgress(int)));
    mResultBuilder = ExecutionResultBuilderPtr(new ExecutionResultBuilder(mPage));

    mCoverageListener = appmodel->getCoverageListener();
    mJavascriptStatistics = appmodel->getJavascriptStatistics();
    mPathTracer = appmodel->getPathTracer();

    QWebExecutionListener::attachListeners();
    webkitListener = QWebExecutionListener::getListener();

    // TODO cleanup in ajax stuff, we are handling ajax through AjaxRequestListener, the ajaxRequest signal and addAjaxCallHandler

    if (enableConstantStringInstrumentation) {
        webkitListener->enableConstantStringInstrumentation();
    }

    QObject::connect(webkitListener, SIGNAL(jqueryEventAdded(QString, QString, QString)),
                     mJquery, SLOT(slEventAdded(QString, QString, QString)));

    QObject::connect(webkitListener, SIGNAL(loadedJavaScript(QString, QSource*)),
                     mCoverageListener.data(), SLOT(slJavascriptScriptParsed(QString, QSource*)));
    QObject::connect(webkitListener, SIGNAL(statementExecuted(uint, QSource*)),
                     mCoverageListener.data(), SLOT(slJavascriptStatementExecuted(uint, QSource*)));
    QObject::connect(webkitListener, SIGNAL(sigJavascriptBytecodeExecuted(QString, uint, QSource*, const ByteCodeInfoStruct)),
                     mCoverageListener.data(), SLOT(slJavascriptBytecodeExecuted(QString, uint, QSource*, const ByteCodeInfoStruct)));
    QObject::connect(webkitListener, SIGNAL(sigJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)),
                     mCoverageListener.data(), SLOT(slJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)));

    QObject::connect(webkitListener, SIGNAL(sigJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)),
                     mPathTracer.data(), SLOT(slJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)));
    QObject::connect(webkitListener, SIGNAL(sigJavascriptFunctionReturned(QString)),
                     mPathTracer.data(), SLOT(slJavascriptFunctionReturned(QString)));
    QObject::connect(mPage.data(), SIGNAL(sigJavascriptAlert(QWebFrame*, QString)),
                     mPathTracer.data(), SLOT(slJavascriptAlert(QWebFrame*, QString)));

    QObject::connect(webkitListener, SIGNAL(sigJavascriptPropertyRead(QString,intptr_t,intptr_t, QSource*)),
                     mJavascriptStatistics.data(), SLOT(slJavascriptPropertyRead(QString,intptr_t,intptr_t, QSource*)));
    QObject::connect(webkitListener, SIGNAL(sigJavascriptPropertyWritten(QString,intptr_t,intptr_t, QSource*)),
                     mJavascriptStatistics.data(), SLOT(slJavascriptPropertyWritten(QString,intptr_t,intptr_t, QSource*)));

    QObject::connect(webkitListener, SIGNAL(addedEventListener(QWebElement*, QString)),
                     mResultBuilder.data(), SLOT(slEventListenerAdded(QWebElement*, QString)));
    QObject::connect(webkitListener, SIGNAL(removedEventListener(QWebElement*, QString)),
                     mResultBuilder.data(), SLOT(slEventListenerRemoved(QWebElement*, QString)));

    QObject::connect(webkitListener, SIGNAL(triggeredEventListener(QWebElement*, QString)),
                     mPathTracer.data(), SLOT(slEventListenerTriggered(QWebElement*, QString)));

    QObject::connect(webkitListener, SIGNAL(addedTimer(int, int, bool)),
                     mResultBuilder.data(), SLOT(slTimerAdded(int, int, bool)));
    QObject::connect(webkitListener, SIGNAL(removedTimer(int)),
                     mResultBuilder.data(), SLOT(slTimerRemoved(int)));

    QObject::connect(webkitListener, SIGNAL(script_crash(QString, intptr_t, int)),
                     mResultBuilder.data(), SLOT(slScriptCrashed(QString, intptr_t, int)));
    QObject::connect(webkitListener, SIGNAL(eval_call(QString)),
                     mResultBuilder.data(), SLOT(slStringEvaled(QString)));

    QObject::connect(webkitListener, SIGNAL(addedAjaxCallbackHandler(int)),
                     mResultBuilder.data(), SLOT(slAjaxCallbackHandlerAdded(int)));
    QObject::connect(webkitListener, SIGNAL(ajax_request(QUrl, QString)),
                     mResultBuilder.data(), SLOT(slAjaxRequestInitiated(QUrl, QString)));

    QObject::connect(webkitListener, SIGNAL(sigJavascriptConstantStringEncountered(QString)),
                     mResultBuilder.data(), SLOT(slJavascriptConstantStringEncountered(QString)));


    // Set up the trace builder and event detectors.
    mTraceBuilder = new TraceBuilder(this);

    // The branch detector.
    QSharedPointer<TraceBranchDetector> branchDetector(new TraceBranchDetector());
    QObject::connect(webkitListener, SIGNAL(sigJavascriptBranchExecuted(bool, Symbolic::Expression*, uint, QSource*, const ByteCodeInfoStruct)),
            branchDetector.data(), SLOT(slBranch(bool, Symbolic::Expression*, uint, QSource*, const ByteCodeInfoStruct)));
    mTraceBuilder->addDetector(branchDetector);

    // The alert detector.
    QSharedPointer<TraceAlertDetector> alertDetector(new TraceAlertDetector());
    QObject::connect(mPage.data(), SIGNAL(sigJavascriptAlert(QWebFrame*, QString)),
                     alertDetector.data(), SLOT(slJavascriptAlert(QWebFrame*, QString)));
    mTraceBuilder->addDetector(alertDetector);

    // The function call detector.
    QSharedPointer<TraceFunctionCallDetector> functionCallDetector(new TraceFunctionCallDetector());
    QObject::connect(webkitListener, SIGNAL(sigJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)),
                     functionCallDetector.data(), SLOT(slJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)));
    mTraceBuilder->addDetector(functionCallDetector);

}

WebKitExecutor::~WebKitExecutor()
{
}

void WebKitExecutor::detach() {
    webkitListener->endSymbolicSession();
    mTraceBuilder->endRecording();

    // ignore events emitted from webkit on deallocation
    webkitListener->disconnect(mResultBuilder.data());
}

void WebKitExecutor::executeSequence(ExecutableConfigurationConstPtr conf)
{
    executeSequence(conf, false);
}

void WebKitExecutor::executeSequence(ExecutableConfigurationConstPtr conf, bool keepOpen)
{
    currentConf = conf;

    mJquery->reset(); // TODO merge into result?
    mResultBuilder->reset();

    qDebug() << "--------------- FETCH PAGE --------------" << endl;

    mCoverageListener->notifyStartingLoad();
    mResultBuilder->notifyStartingLoad();
    mJavascriptStatistics->notifyStartingLoad();
    mPathTracer->notifyStartingLoad();

    webkitListener->beginSymbolicSession();
    mKeepOpen = keepOpen;

    mPage->mainFrame()->load(conf->getUrl());
}

void WebKitExecutor::slLoadProgress(int i){
    if(!mNextOpCanceled)
        qDebug() << "Page loaded " << i << "%";
    mNextOpCanceled = false;
}


void WebKitExecutor::slNAMFinished(QNetworkReply* reply){
    switch(reply->error()){
    case QNetworkReply::NoError:
        break;
    case QNetworkReply::OperationCanceledError:
        mNextOpCanceled = true;
        break;
    default:
        qDebug() << "REPLY" << reply->errorString();

    }

}

void WebKitExecutor::slLoadFinished(bool ok)
{
    if(mNextOpCanceled){
        mNextOpCanceled = false;
        qDebug() << "Page load canceled";
        return;
    }

    if(!ok){
        QString html = mPage->mainFrame()->toHtml();
        if(html == "<html><head></head><body></body></html>"){
            emit sigAbortedExecution(QString("Error: The requested URL ") + currentConf->getUrl().toString() + QString(" could not be loaded"));
            return;
        }        
    }
    mResultBuilder->notifyPageLoaded();

    // Populate forms (preset)

    foreach(QString f , mPresetFields.keys()) {
        QWebElement elm = mPage->mainFrame()->findFirstElement(f);

        if (elm.isNull()) {
            qDebug() << "Warning, preset field " << f << "not found.";
            continue;
        }

        qDebug() << "Setting value " << mPresetFields[f] << "for element " << f << endl;
        elm.setAttribute("value", mPresetFields[f]);
    }

    // Execute input sequence

    qDebug() << "\n------------ EXECUTE SEQUENCE -----------" << endl;

    mTraceBuilder->beginRecording();

    foreach(QSharedPointer<const BaseInput> input, currentConf->getInputSequence()->toList()) {
        mResultBuilder->notifyStartingEvent();
        mCoverageListener->notifyStartingEvent(input);
        mJavascriptStatistics->notifyStartingEvent(input);
        mPathTracer->notifyStartingEvent(input);

        input->apply(this->mPage, this->webkitListener);
    }

    if (!mKeepOpen) {
        webkitListener->endSymbolicSession();
    }

    // End the trace recording in all cases. In concolic mode this is the trace we want, in manual mode we will be recording our own traces anyway.
    mTraceBuilder->endRecording();

    // TODO: This was previously enclosed by if(!mKeepOpen). This means no post-load analysis can be done in demo mode. What are tyhe implications of changing this? Which other parts will depend on this?
    emit sigExecutedSequence(currentConf, mResultBuilder->getResult());


    mKeepOpen = false;
}

ArtemisWebPagePtr WebKitExecutor::getPage()
{
    return mPage;
}

TraceBuilder* WebKitExecutor::getTraceBuilder()
{
    return mTraceBuilder;
}

}
