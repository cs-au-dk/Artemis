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
#include "concolic/concolicanalysis.h"

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
    void execute(ConcolicAdviceCommand* command);
    void execute(EvaluateJsCommand* command);
    void execute(SetSymbolicValuesCommand* command);
    void execute(CoverageCommand* command);

protected:
    virtual void done();

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

    void notifyStartingEvent(QString event, QString elementXPath);

    // Concolic advice
    void concolicInit();
    void concolicInitPage(QSharedPointer<ExecutionResult> result);
    QVariant concolicBeginTrace(QString sequence, bool implicitEndTrace);
    QVariant concolicEndTrace(QString sequence);
    QVariant concolicAdvice(QString sequence, uint amount, bool allowDuringTrace);
    QVariant concolicStatistics(QString sequence);
    QString concolicSymbolToXPath(QString sequence, QString symbol);
    QVariant concolicResponseOk();
    void concolicCreateNewAnalysis(QString sequence);
    void concolicOutputTree(TraceNodePtr tree, QString name);
    QString mConcolicSequenceRecording;
    QMap<QString, ConcolicAnalysisPtr> mConcolicTrees;
    uint mConcolicTraceMarkerIdx;
    QMap<QString, QList<FormFieldDescriptorConstPtr> > mConcolicFormFields; // Must be defined wherever mConcolicTrees is.
    QList<FormFieldDescriptorConstPtr> mConcolicFormFieldsForPage;
    QMap<QString, QPair<QString, QString> > mConcolicTreeOutputFileNames;
    uint mConcolicTreeOutputFileNameCounter;

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

    // GUI part
    void slDebugWindowClosed();

    // Concolic advice:
    void slExecutionTreeUpdated(TraceNodePtr tree, QString name);

signals:
    void sigCommandFinished(QVariant response);

    // Concolic advice
    void sigNewTraceMarker(QString label, QString index, bool isSelectRestriction, SelectRestriction selectRestriction);
};


} //namespace artemis
#endif // ANALYSISSERVERRUNTIME_H
