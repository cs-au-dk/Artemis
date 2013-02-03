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
#include "util/coverageutil.h"

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
    currentResult = NULL;

    mPresetFields = presetFields;
    mJquery = jqueryListener;

    ajaxListener = ajaxListener;
    ajaxListener->setParent(this);

    covList = new CoverageListener(this);

    webkitListener = new QWebExecutionListener();
    webkitListener->installWebKitExecutionListener(webkitListener);

    // TODO cleanup in ajax stuff, we are handling ajax through AjaxRequestListener, the ajaxRequest signal and addAjaxCallHandler

    QObject::connect(webkitListener, SIGNAL(scriptCrash(QString, intptr_t, int)),
                     this, SLOT(slScriptCrash(QString, intptr_t, int)));
    QObject::connect(webkitListener, SIGNAL(ajaxRequest(QUrl, QString)),
                     this, SLOT(slAjaxRequest(QUrl, QString)));
    QObject::connect(webkitListener, SIGNAL(loadedJavaScript(intptr_t, QString, QUrl, int)),
                     this, SLOT(slCodeLoaded(intptr_t, QString, QUrl, int)));

    QObject::connect(webkitListener, SIGNAL(jqueryEventAdded(QString, QString, QString)),
                     mJquery, SLOT(slEventAdded(QString, QString, QString)));

    QObject::connect(webkitListener, SIGNAL(loadedJavaScript(intptr_t, QString, QUrl, int)),
                     covList, SLOT(newCode(intptr_t, QString, QUrl, int)));
    QObject::connect(webkitListener, SIGNAL(statementExecuted(intptr_t, std::string, int)),
                     covList, SLOT(statementExecuted(intptr_t, std::string, int)));

    page = new ArtemisWebPage(this);
    page->setNetworkAccessManager(ajaxListener);

    QObject::connect(page, SIGNAL(loadFinished(bool)),
                     this, SLOT(slLoadFinished(bool)));

}

WebKitExecutor::~WebKitExecutor()
{
    //delete currentConf;
    //delete currentResult;
    delete page;
    delete covList;
}

void WebKitExecutor::executeSequence(QSharedPointer<ExecutableConfiguration> conf)
{
    qDebug() << "Artemis: Executing sequence" << endl;

    if (currentResult != 0) {
        qDebug() << "Removing old result" << endl;

        currentResult->disconnect();

        delete currentResult;
    }

    currentResult = new ExecutionResult(0);
    currentConf = conf;

    mJquery->reset();

    QObject::connect(webkitListener, SIGNAL(addedEventListener(QWebElement*, QString)),
                     currentResult, SLOT(newEventListener(QWebElement*, QString)));
    QObject::connect(webkitListener, SIGNAL(removedEventListener(QWebElement*, QString)),
                     currentResult, SLOT(removeEventListener(QWebElement*, QString)));

    QObject::connect(webkitListener, SIGNAL(addedAjaxCallbackHandler(int)),
                     currentResult, SLOT(addedAjaxCallbackHandler(int)));

    QObject::connect(webkitListener, SIGNAL(addedTimer(int, int, bool)),
                     currentResult, SLOT(slTimerAdded(int, int, bool)));
    QObject::connect(webkitListener, SIGNAL(removedTimer(int)),
                     currentResult, SLOT(slTimerRemoved(int)));

    QObject::connect(webkitListener, SIGNAL(scriptCrash(QString, intptr_t, int)),
                     currentResult, SLOT(slScriptCrash(QString, intptr_t, int)));
    QObject::connect(webkitListener, SIGNAL(evalCall(QString)),
                     currentResult, SLOT(slEvalString(QString)));

    //Load URL into WebKit
    qDebug() << "Trying to load: " << conf->getUrl().toString() << endl;
    page->mainFrame()->load(conf->getUrl());
}

void WebKitExecutor::slLoadFinished(bool ok)
{

    if (!ok) {
        qDebug() << "WEBKIT: Website load failed!";

        currentResult->makeLoadFailed();
        finishedExecutionSequence();

        exit(1);
        return;
    }

    qDebug() << "WEBKIT: Finished loading" << endl;

    //handleAjaxCallbacks();
    setupInitial();;
    doExe();
    finishedExecutionSequence();
}

void WebKitExecutor::saveDomState()
{
    currentResult->setStateHash(qHash(page->mainFrame()->toHtml()));
    currentResult->setModfiedDom(page->mainFrame()->toHtml().localeAwareCompare(this->initialPageState) != 0);
    currentResult->setPageContents(page->mainFrame()->toHtml());
}

void WebKitExecutor::setupInitial()
{
    //Save the page state
    this->initialPageState = page->mainFrame()->toHtml();

    //Set preset formfields
    foreach(QString f , mPresetFields.keys()) {
        QWebElement elm = page->mainFrame()->findFirstElement(f);

        if (elm.isNull())
            { continue; }

        qDebug() << "Setting value " << mPresetFields[f] << "for element " << f << endl;
        elm.setAttribute("value", mPresetFields[f]);
    }

}

void WebKitExecutor::doExe()
{
    QSharedPointer<const InputSequence> seq = currentConf->getInputSequence();

    foreach(QSharedPointer<const BaseInput> input, seq->toList()) {
        qDebug() << "APPLY!" << endl;
        input->apply(this->page, this->webkitListener);
        //Wait for any ajax stuff to finish
        //            handleAjaxCallbacks();
    }
}

void WebKitExecutor::getFormFields()
{
    QSet<QWebFrame*> ff = allFrames();

    foreach(QWebFrame * f, ff) {
        QWebElementCollection inputs = f->findAllElements("input");
        foreach(QWebElement i, inputs) {
            FormFieldTypes fType =  getTypeFromAttr(i.attribute("type"));

            if (fType == NO_INPUT)
                { continue; }

            QSharedPointer<FormField> formf = QSharedPointer<FormField>(new FormField(fType, new DOMElementDescriptor(0, &i)));
            currentResult->addFormField(formf);
        }

        //Gather <textarea> elements
        QWebElementCollection textareas = f->findAllElements("textarea");
        foreach(QWebElement ta, textareas) {
            QSharedPointer<FormField> taf = QSharedPointer<FormField>(new FormField(TEXT, new DOMElementDescriptor(0, &ta)));
            currentResult->addFormField(taf);
        }

        //Gather select tags
        QWebElementCollection selects = f->findAllElements("select");
        foreach(QWebElement ss, selects) {
            QSet<QString> options = getSelectOptions(ss);
            QSharedPointer<FormField> ssf = QSharedPointer<FormField>(new FormField(FIXED_INPUT, new DOMElementDescriptor(0, &ss), options));
            currentResult->addFormField(ssf);
        }
    }
}

QSet<QString> WebKitExecutor::getSelectOptions(const QWebElement& e)
{
    QSet<QString> res;
    QWebElementCollection options = e.findAll("option");
    foreach(QWebElement o, options) {
        QString valueAttr = o.attribute("value");

        if (!valueAttr.isEmpty())
            { valueAttr = o.toPlainText(); }

        if (valueAttr.isEmpty()) {
            qWarning() << "WARN: Found empty option element in select, ignoring";
            continue;
        }

        res << valueAttr;
    }
    return res;
}

QSet<QWebFrame*> WebKitExecutor::allFrames()
{
    QSet<QWebFrame*> res;
    QWebFrame* main = page->mainFrame();
    res.insert(main);
    QList<QWebFrame*> worklist;
    worklist.append(main);

    while (!worklist.isEmpty()) {
        QWebFrame* c = worklist.takeFirst();
        worklist += c->childFrames();
        res += c->childFrames().toSet();
    }

    return res;
}

void WebKitExecutor::finishUp()
{
    if (currentResult != 0) {
        qDebug() << "Removing old result" << endl;

        writeCoverageHtml(coverage());

        currentResult->disconnect();

        delete currentResult;
    }
}

void WebKitExecutor::finishedExecutionSequence()
{
    getFormFields();
    saveDomState();

    currentResult->finalize();

    emit sigExecutedSequence(currentConf, currentResult);
}

CodeCoverage WebKitExecutor::coverage()
{
    return covList->currentCoverage();
}

void WebKitExecutor::slScriptCrash(QString ca, intptr_t id, int n)
{
    qDebug() << "Script crashed";
}

void WebKitExecutor::slAjaxRequest(QUrl u, QString postData)
{
    AjaxRequest req = AjaxRequest(u, postData);
    qDebug() << "Adding AJAX request: " << req;
    this->currentResult->addAjaxRequest(req);
}

void WebKitExecutor::slEvalCalled(QString evalText)
{
    qDebug() << "Dynamic code eval: " << evalText;
}

void WebKitExecutor::slCodeLoaded(intptr_t _, QString src, QUrl url, int li)
{
    qDebug() << "WebKitExecutor::slCodeLoaded" << endl;
}
}
