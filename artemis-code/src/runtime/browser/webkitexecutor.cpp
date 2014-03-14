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

#include <iostream>
#include <unistd.h>

#include <QtWebKit>
#include <QSource>
#include <QApplication>
#include <QStack>
#include <QDebug>
#include <QWebExecutionListener>

#include "runtime/input/forms/formfielddescriptor.h"
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
                               QMap<QString, InjectionValue> presetFields,
                               JQueryListener* jqueryListener,
                               AjaxRequestListener* ajaxListener,
                               bool enableConstantStringInstrumentation,
                               bool enablePropertyAccessInstrumentation) :
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
    mWebkitListener = QWebExecutionListener::getListener();

    // TODO cleanup in ajax stuff, we are handling ajax through AjaxRequestListener, the ajaxRequest signal and addAjaxCallHandler

    if (enableConstantStringInstrumentation) {
        mWebkitListener->enableConstantStringInstrumentation();
    }

    if (enablePropertyAccessInstrumentation) {
        mWebkitListener->enablePropertyAccessInstrumentation();
    }

    QObject::connect(mWebkitListener, SIGNAL(jqueryEventAdded(QString, QString, QString)),
                     mJquery, SLOT(slEventAdded(QString, QString, QString)));

    QObject::connect(mWebkitListener, SIGNAL(loadedJavaScript(QString, QSource*)),
                     mCoverageListener.data(), SLOT(slJavascriptScriptParsed(QString, QSource*)));
    QObject::connect(mWebkitListener, SIGNAL(statementExecuted(uint, QSource*)),
                     mCoverageListener.data(), SLOT(slJavascriptStatementExecuted(uint, QSource*)));
    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptBytecodeExecuted(const ByteCodeInfoStruct, uint, QSource*)),
                     mCoverageListener.data(), SLOT(slJavascriptBytecodeExecuted(const ByteCodeInfoStruct, uint, QSource*)));
    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)),
                     mCoverageListener.data(), SLOT(slJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)));

    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)),
                     mPathTracer.data(), SLOT(slJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)));
    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptFunctionReturned(QString)),
                     mPathTracer.data(), SLOT(slJavascriptFunctionReturned(QString)));
    QObject::connect(mPage.data(), SIGNAL(sigJavascriptAlert(QWebFrame*, QString)),
                     mPathTracer.data(), SLOT(slJavascriptAlert(QWebFrame*, QString)));

    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptPropertyRead(QString,intptr_t,intptr_t, QSource*)),
                     mJavascriptStatistics.data(), SLOT(slJavascriptPropertyRead(QString,intptr_t,intptr_t, QSource*)));
    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptPropertyWritten(QString,intptr_t,intptr_t, QSource*)),
                     mJavascriptStatistics.data(), SLOT(slJavascriptPropertyWritten(QString,intptr_t,intptr_t, QSource*)));

    QObject::connect(mWebkitListener, SIGNAL(addedEventListener(QWebElement*, QString)),
                     mResultBuilder.data(), SLOT(slEventListenerAdded(QWebElement*, QString)));
    QObject::connect(mWebkitListener, SIGNAL(removedEventListener(QWebElement*, QString)),
                     mResultBuilder.data(), SLOT(slEventListenerRemoved(QWebElement*, QString)));

    QObject::connect(mWebkitListener, SIGNAL(triggeredEventListener(QWebElement*, QString)),
                     mPathTracer.data(), SLOT(slEventListenerTriggered(QWebElement*, QString)));

    QObject::connect(mWebkitListener, SIGNAL(addedTimer(int, int, bool)),
                     mResultBuilder.data(), SLOT(slTimerAdded(int, int, bool)));
    QObject::connect(mWebkitListener, SIGNAL(removedTimer(int)),
                     mResultBuilder.data(), SLOT(slTimerRemoved(int)));

    QObject::connect(mWebkitListener, SIGNAL(script_crash(QString, intptr_t, int)),
                     mResultBuilder.data(), SLOT(slScriptCrashed(QString, intptr_t, int)));
    QObject::connect(mWebkitListener, SIGNAL(eval_call(QString)),
                     mResultBuilder.data(), SLOT(slStringEvaled(QString)));

    QObject::connect(mWebkitListener, SIGNAL(addedAjaxCallbackHandler(int)),
                     mResultBuilder.data(), SLOT(slAjaxCallbackHandlerAdded(int)));
    QObject::connect(mWebkitListener, SIGNAL(ajax_request(QUrl, QString)),
                     mResultBuilder.data(), SLOT(slAjaxRequestInitiated(QUrl, QString)));

    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptConstantStringEncountered(QString)),
                     mResultBuilder.data(), SLOT(slJavascriptConstantStringEncountered(QString)));


    // Set up the trace builder and event detectors.
    mTraceBuilder = new TraceBuilder(this);

    // The branch detector.
    QSharedPointer<TraceBranchDetector> branchDetector(new TraceBranchDetector());
    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptBranchExecuted(bool, Symbolic::Expression*, uint, QSource*, const ByteCodeInfoStruct)),
            branchDetector.data(), SLOT(slBranch(bool, Symbolic::Expression*, uint, QSource*, const ByteCodeInfoStruct)));
    mTraceBuilder->addDetector(branchDetector);

    // The alert detector.
    QSharedPointer<TraceAlertDetector> alertDetector(new TraceAlertDetector());
    QObject::connect(mPage.data(), SIGNAL(sigJavascriptAlert(QWebFrame*, QString)),
                     alertDetector.data(), SLOT(slJavascriptAlert(QWebFrame*, QString)));
    mTraceBuilder->addDetector(alertDetector);

    // The function call detector.
    QSharedPointer<TraceFunctionCallDetector> functionCallDetector(new TraceFunctionCallDetector());
    QObject::connect(mWebkitListener, SIGNAL(sigJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)),
                     functionCallDetector.data(), SLOT(slJavascriptFunctionCalled(QString, size_t, uint, uint, QSource*)));
    mTraceBuilder->addDetector(functionCallDetector);

    // The page load detector
    QSharedPointer<TracePageLoadDetector> pageLoadDetector(new TracePageLoadDetector());
    QObject::connect(mWebkitListener, SIGNAL(sigPageLoadScheduled(QUrl)),
                     pageLoadDetector.data(), SLOT(slPageLoad(QUrl)));
    mTraceBuilder->addDetector(pageLoadDetector);

    // The event marker detector is created and connected in the concolic runtime.

    // The DOM modification "detector".
    QSharedPointer<TraceDomModDetector> domModDetector(new TraceDomModDetector());
    QObject::connect(mResultBuilder.data(), SIGNAL(sigDomModified(QString, QString)),
                     domModDetector.data(), SLOT(slDomModified(QString, QString)));
    mTraceBuilder->addDetector(domModDetector);


}

WebKitExecutor::~WebKitExecutor()
{
}

void WebKitExecutor::detach() {
    mWebkitListener->endSymbolicSession();
    mTraceBuilder->endRecording();

    // ignore events emitted from webkit on deallocation
    mWebkitListener->disconnect(mResultBuilder.data());
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

    mWebkitListener->beginSymbolicSession();
    mWebkitListener->clearAjaxCallbacks(); // reset the ajax callback ids

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

        qDebug() << "Setting value " << mPresetFields[f].toString() << "for element " << f;

        FormFieldInjector::inject(elm, mPresetFields[f]);
    }

    // Execute input sequence

    qDebug() << "\n------------ EXECUTE SEQUENCE -----------" << endl;

    mTraceBuilder->beginRecording();

    foreach(QSharedPointer<const BaseInput> input, currentConf->getInputSequence()->toList()) {

        mResultBuilder->notifyStartingEvent();
        mCoverageListener->notifyStartingEvent(input);
        mJavascriptStatistics->notifyStartingEvent(input);
        mPathTracer->notifyStartingEvent(input);

        mPage->updateFormIdentifiers();

        input->apply(this->mPage, this->mWebkitListener);
    }

    if (!mKeepOpen) {
        mWebkitListener->endSymbolicSession();
    }

    // Get the result of this execution.
    // N.B. This sends some statistics to the trace recorder, so we call it before ending the trace.
    QSharedPointer<ExecutionResult> result = mResultBuilder->getResult();

    // End the trace recording.
    mTraceBuilder->endRecording();

    // TODO: This was previously enclosed by if(!mKeepOpen). This means no post-load analysis can be done in demo mode. What are tyhe implications of changing this? Which other parts will depend on this?
    emit sigExecutedSequence(currentConf, result);


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
