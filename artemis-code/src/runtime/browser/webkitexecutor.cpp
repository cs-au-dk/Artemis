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
#include <QApplication>
#include <QStack>
#include <QDebug>
#include <qwebexecutionlistener.h>
#include <instrumentation/executionlistener.h>

#include "runtime/input/forms/formfield.h"
#include "runtime/input/events/domelementdescriptor.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "runtime/input/baseinput.h"

#include "webkitexecutor.h"

using namespace std;

namespace artemis
{

WebKitExecutor::WebKitExecutor(QObject* parent,
                               AppModelPtr appmodel,
                               QMap<QString, QString> presetFields,
                               JQueryListener* jqueryListener,
                               AjaxRequestListener* ajaxListener) :
    QObject(parent)
{

    mPresetFields = presetFields;
    mJquery = jqueryListener;

    mAjaxListener = ajaxListener;
    mAjaxListener->setParent(this);

    mPage = new ArtemisWebPage(this);
    mPage->setNetworkAccessManager(mAjaxListener);

    QObject::connect(mPage, SIGNAL(loadFinished(bool)),
                     this, SLOT(slLoadFinished(bool)));

    mResultBuilder = new ExecutionResultBuilder(this, mPage);

    mCoverageListener = appmodel->getCoverageListener();
    mJavascriptStatistics = appmodel->getJavascriptStatistics();

    QWebExecutionListener::attachListeners();
    webkitListener = QWebExecutionListener::getListener();

    // TODO cleanup in ajax stuff, we are handling ajax through AjaxRequestListener, the ajaxRequest signal and addAjaxCallHandler

    QObject::connect(webkitListener, SIGNAL(jqueryEventAdded(QString, QString, QString)),
                     mJquery, SLOT(slEventAdded(QString, QString, QString)));

    QObject::connect(webkitListener, SIGNAL(loadedJavaScript(intptr_t, QString, QUrl, int)),
                     mCoverageListener.data(), SLOT(newCode(intptr_t, QString, QUrl, int)));
    QObject::connect(webkitListener, SIGNAL(statementExecuted(intptr_t, int)),
                     mCoverageListener.data(), SLOT(statementExecuted(intptr_t, int)));
    QObject::connect(webkitListener, SIGNAL(sigJavascriptBytecodeExecuted(intptr_t, size_t)),
                     mCoverageListener.data(), SLOT(slJavascriptBytecodeExecuted(intptr_t, size_t)));
    QObject::connect(webkitListener, SIGNAL(sigJavascriptFunctionCalled(intptr_t,QString,size_t)),
                     mCoverageListener.data(), SLOT(slJavascriptFunctionCalled(intptr_t,QString,size_t)));

    QObject::connect(webkitListener, SIGNAL(sigJavascriptPropertyRead(QString,intptr_t,intptr_t,QUrl,int)),
                     mJavascriptStatistics.data(), SLOT(slJavascriptPropertyRead(QString,intptr_t,intptr_t,QUrl,int)));
    QObject::connect(webkitListener, SIGNAL(sigJavascriptPropertyWritten(QString,intptr_t,intptr_t,QUrl,int)),
                     mJavascriptStatistics.data(), SLOT(slJavascriptPropertyWritten(QString,intptr_t,intptr_t,QUrl,int)));

    QObject::connect(webkitListener, SIGNAL(addedEventListener(QWebElement*, QString)),
                     mResultBuilder, SLOT(slEventListenerAdded(QWebElement*, QString)));
    QObject::connect(webkitListener, SIGNAL(removedEventListener(QWebElement*, QString)),
                     mResultBuilder, SLOT(slEventListenerRemoved(QWebElement*, QString)));

    QObject::connect(webkitListener, SIGNAL(addedTimer(int, int, bool)),
                     mResultBuilder, SLOT(slTimerAdded(int, int, bool)));
    QObject::connect(webkitListener, SIGNAL(removedTimer(int)),
                     mResultBuilder, SLOT(slTimerRemoved(int)));

    QObject::connect(webkitListener, SIGNAL(script_crash(QString, intptr_t, int)),
                     mResultBuilder, SLOT(slScriptCrashed(QString, intptr_t, int)));
    QObject::connect(webkitListener, SIGNAL(eval_call(QString)),
                     mResultBuilder, SLOT(slStringEvaled(QString)));

    QObject::connect(webkitListener, SIGNAL(addedAjaxCallbackHandler(int)),
                     mResultBuilder, SLOT(slAjaxCallbackHandlerAdded(int)));
    QObject::connect(webkitListener, SIGNAL(ajax_request(QUrl, QString)),
                     mResultBuilder, SLOT(slAjaxRequestInitiated(QUrl, QString)));

    QObject::connect(webkitListener, SIGNAL(sigJavascriptConstantEncountered(QString)),
                     mResultBuilder, SLOT(slJavascriptConstantEncountered(QString)));

}

WebKitExecutor::~WebKitExecutor()
{
}

void WebKitExecutor::detach() {

    // ignore events emitted from webkit on deallocation
    webkitListener->disconnect(mResultBuilder);

}

void WebKitExecutor::executeSequence(ExecutableConfigurationConstPtr conf)
{
    currentConf = conf;

    mJquery->reset(); // TODO merge into result?
    mResultBuilder->reset();

    qDebug() << "--------------- FETCH PAGE --------------" << endl;

    mCoverageListener->notifyStartingLoad();
    mResultBuilder->notifyStartingLoad();
    mJavascriptStatistics->notifyStartingLoad();

    mPage->mainFrame()->load(conf->getUrl());
}

void WebKitExecutor::slLoadFinished(bool ok)
{
    mResultBuilder->notifyPageLoaded();

    if (!ok) {
        qWarning() << "WEBKIT: Website load failed!";
        exit(1);
    }

    // Populate forms (preset)

    foreach(QString f , mPresetFields.keys()) {
        QWebElement elm = mPage->mainFrame()->findFirstElement(f);

        if (elm.isNull()) {
            continue;
        }

        qDebug() << "Setting value " << mPresetFields[f] << "for element " << f << endl;
        elm.setAttribute("value", mPresetFields[f]);
    }

    // Execute input sequence

    qDebug() << "\n------------ EXECUTE SEQUENCE -----------" << endl;

    foreach(QSharedPointer<const BaseInput> input, currentConf->getInputSequence()->toList()) {
        mResultBuilder->notifyStartingEvent();
        mCoverageListener->notifyStartingEvent(input);
        mJavascriptStatistics->notifyStartingEvent(input);
        input->apply(this->mPage, this->webkitListener);
    }

    // DONE

    emit sigExecutedSequence(currentConf, mResultBuilder->getResult());
}

}
