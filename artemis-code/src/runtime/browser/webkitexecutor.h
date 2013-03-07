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

#ifndef WEBKITEXECUTOR_H
#define WEBKITEXECUTOR_H

#include <QObject>
#include <QSemaphore>
#include <QtWebKit>
#include <QtWebKit/qwebexecutionlistener.h>
#include <QSharedPointer>

#include "artemisglobals.h"

#include "runtime/executableconfiguration.h"
#include "runtime/browser/ajax/ajaxrequestlistener.h"
#include "model/coverage/coveragelistener.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"

#include "executionresult.h"
#include "executionresultbuilder.h"
#include "artemiswebpage.h"
#include "runtime/appmodel.h"

namespace artemis
{

class WebKitExecutor : public QObject
{
    Q_OBJECT

public:
    WebKitExecutor(QObject* parent,
                   AppModelPtr appmodel,
                   QMap<QString, QString> presetFields,
                   JQueryListener* jqueryListener,
                   AjaxRequestListener* ajaxListener);
    ~WebKitExecutor();

    void executeSequence(ExecutableConfigurationConstPtr conf);
    void detach();

    QWebExecutionListener* webkitListener; // TODO should not be public

private:
    ArtemisWebPagePtr mPage;
    ExecutionResultBuilderPtr mResultBuilder;
    ExecutableConfigurationConstPtr currentConf;
    AjaxRequestListener* mAjaxListener;
    JQueryListener* mJquery;
    QMap<QString, QString> mPresetFields;

    CoverageListenerPtr mCoverageListener;
    JavascriptStatisticsPtr mJavascriptStatistics;

signals:
    void sigExecutedSequence(ExecutableConfigurationConstPtr conf, QSharedPointer<ExecutionResult> res);
    void sigAbortedExecution(QString reason);

public slots:
    void slLoadFinished(bool ok);


};

}
#endif // WEBKITEXECUTOR_H
