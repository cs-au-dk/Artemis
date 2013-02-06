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

#ifndef WEBKITEXECUTOR_H
#define WEBKITEXECUTOR_H

#include <QObject>
#include <QSemaphore>
#include <QtWebKit>
#include <QtWebKit/qwebexecutionlistener.h>
#include <QSharedPointer>

#include "artemisglobals.h"

#include "runtime/executableconfiguration.h"
#include "runtime/ajax/ajaxrequestlistener.h"
#include "coverage/coveragelistener.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"

#include "executionresult.h"
#include "executionresultbuilder.h"
#include "artemiswebpage.h"

namespace artemis
{

class WebKitExecutor : public QObject
{
    Q_OBJECT

public:
    WebKitExecutor(QObject* parent,
                   QMap<QString, QString> presetFields,
                   JQueryListener* jqueryListener,
                   AjaxRequestListener* ajaxListener);
    ~WebKitExecutor();

    void executeSequence(QSharedPointer<ExecutableConfiguration> conf);
    void detach();
    CodeCoverage coverage();

    QWebExecutionListener* webkitListener; // TODO should not be public

private:
    ArtemisWebPage* mPage;
    ExecutionResultBuilder* mResultBuilder;
    QSharedPointer<ExecutableConfiguration> currentConf;
    CoverageListener* covList;
    AjaxRequestListener* mAjaxListener;
    JQueryListener* mJquery;
    QMap<QString, QString> mPresetFields;

signals:
    void sigExecutedSequence(QSharedPointer<ExecutableConfiguration> conf, QSharedPointer<ExecutionResult> res);

public slots:
    void slLoadFinished(bool ok);


};

}
#endif // WEBKITEXECUTOR_H
