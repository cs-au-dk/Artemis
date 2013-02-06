/*
  Copyright 2011 Simon Holm Jensen. All rights reserved.

  Redistribution and use in source and binary forms, with or without modification, are
  permitted provided that the following conditions are met:

     1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.

     2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.

  THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
  WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  The views and conclusions contained in the software and documentation are those of the
  authors and should not be interpreted as representing official policies, either expressed
  or implied, of Simon Holm Jensen
*/

#include <iostream>
#include <unistd.h>

#include <QtWebKit>
#include <QApplication>
#include <QStack>
#include <QDebug>
#include <qwebexecutionlistener.h>
#include <instrumentation/executionlistener.h>

#include "runtime/events/forms/formfield.h"
#include "runtime/events/domelementdescriptor.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "runtime/input/baseinput.h"

#include "webkitexecutor.h"

using namespace std;

namespace artemis
{

WebKitExecutor::WebKitExecutor(QObject* parent,
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
    covList = new CoverageListener(this);

    webkitListener = new QWebExecutionListener();
    webkitListener->installWebKitExecutionListener(webkitListener);

    // TODO cleanup in ajax stuff, we are handling ajax through AjaxRequestListener, the ajaxRequest signal and addAjaxCallHandler

    QObject::connect(webkitListener, SIGNAL(jqueryEventAdded(QString, QString, QString)),
                     mJquery, SLOT(slEventAdded(QString, QString, QString)));

    QObject::connect(webkitListener, SIGNAL(loadedJavaScript(intptr_t, QString, QUrl, int)),
                     covList, SLOT(newCode(intptr_t, QString, QUrl, int)));
    QObject::connect(webkitListener, SIGNAL(statementExecuted(intptr_t, std::string, int)),
                     covList, SLOT(statementExecuted(intptr_t, std::string, int)));

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
    QObject::connect(webkitListener, SIGNAL(loadedJavaScript(intptr_t, QString, QUrl, int)),
                     mResultBuilder, SLOT(slCodeLoaded(intptr_t, QString, QUrl, int)));

    QObject::connect(webkitListener, SIGNAL(addedAjaxCallbackHandler(int)),
                     mResultBuilder, SLOT(slAjaxCallbackHandlerAdded(int)));
    QObject::connect(webkitListener, SIGNAL(ajax_request(QUrl, QString)),
                     mResultBuilder, SLOT(slAjaxRequestInitiated(QUrl, QString)));

}

WebKitExecutor::~WebKitExecutor()
{
}

void WebKitExecutor::detach() {

    // ignore events emitted from webkit on deallocation
    webkitListener->disconnect(mResultBuilder);

}

void WebKitExecutor::executeSequence(QSharedPointer<ExecutableConfiguration> conf)
{
    qDebug() << "Artemis: Executing sequence" << endl;

    currentConf = conf;

    mJquery->reset(); // TODO merge into result?
    mResultBuilder->reset();

    qDebug() << "Trying to load: " << conf->getUrl().toString() << endl;
    mPage->mainFrame()->load(conf->getUrl());
}

void WebKitExecutor::slLoadFinished(bool ok)
{
    mResultBuilder->notifyPageLoaded();

    if (!ok) {
        qWarning("WEBKIT: Website load failed!");
        exit(1);
    }

    qDebug() << "WEBKIT: Finished loading" << endl;

    // Populate forms

    foreach(QString f , mPresetFields.keys()) {
        QWebElement elm = mPage->mainFrame()->findFirstElement(f);

        if (elm.isNull()) {
            continue;
        }

        qDebug() << "Setting value " << mPresetFields[f] << "for element " << f << endl;
        elm.setAttribute("value", mPresetFields[f]);
    }

    // Execute input sequence

    foreach(QSharedPointer<const BaseInput> input, currentConf->getInputSequence()->toList()) {
        input->apply(this->mPage, this->webkitListener);
    }

    // DONE

    emit sigExecutedSequence(currentConf, mResultBuilder->getResult());
}

CodeCoverage WebKitExecutor::coverage()
{
    return covList->currentCoverage();
}

}
