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

#ifndef ANALYSISSERVERRUNTIME_H
#define ANALYSISSERVERRUNTIME_H

#include <QObject>

#include "runtime/runtime.h"
#include "runtime/analysisserver/analysisserver.h"
#include "runtime/analysisserver/fieldreadlog.h"
#include "runtime/browser/artemiswebview.h"

namespace artemis
{


class AnalysisServerRuntime : public Runtime
{
    Q_OBJECT

public:
    AnalysisServerRuntime(QObject* parent, const Options& options, const QUrl& url);

    void run(const QUrl& url);

    // Different methods to execute the different types of command.
    void execute(Command* command);
    void execute(ExitCommand* command);
    void execute(ErrorCommand* command);
    void execute(EchoCommand* command);
    void execute(PageLoadCommand* command);
    void execute(HandlersCommand* command);
    void execute(ClickCommand* command);
    void execute(PageStateCommand* command);
    void execute(ElementCommand* command);
    void execute(FieldsReadCommand* command);
    void execute(BackButtonCommand* command);
    void execute(FormInputCommand* command);
    void execute(XPathCommand* command);
    void execute(EventTriggerCommand* command);
    void execute(WindowSizeCommand* command);

protected:
    AnalysisServer mAnalysisServer;

    ArtemisWebViewPtr mWebView;
    void setWindowSize(int width, int height);

    QVariant errorResponse(QString message);
    void emitTimeout();

    enum ServerState {
        IDLE, EXIT, PAGELOAD_BLANK, PAGELOAD, PAGELOAD_TIMEOUT, PAGELOAD_WAITING_REDIRECT, PAGELOAD_BACK_BUTTON
    };
    ServerState mServerState;
    CommandPtr mCurrentCommand;

    bool mIsPageLoaded;
    bool mIsScheduledRedirection;

    void loadUrl(QUrl url);

    void backButtonOrError();

    // Page analysis
    FieldReadLog mFieldReadLog;

protected slots:
    // Server part
    void slExecuteCommand(CommandPtr command);
    void slResponseFinished();
    void slLoadTimeoutTriggered();

    // Browser part
    void slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result);
    void slNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, QWebPage::NavigationType type);
    void slPageLoadScheduled(QUrl url);
    virtual void slAbortedExecution(QString reason);

signals:
    void sigCommandFinished(QVariant response);

};


} //namespace artemis
#endif // ANALYSISSERVERRUNTIME_H
