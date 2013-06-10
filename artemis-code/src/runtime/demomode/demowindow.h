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


#ifndef DEMOWINDOW_H
#define DEMOWINDOW_H



#include <QtGui>
#include <QLineEdit>
#include <QSharedPointer>
#include <QUrl>
#include <QList>
#include <QPair>

#include "runtime/browser/artemiswebview.h"
#include "runtime/browser/webkitexecutor.h"
#include "artemisbrowserwidget.h"
#include "initialanalysiswidget.h"

#include "concolic/entrypoints.h"
#include "concolic/trace.h"
#include "concolic/tracebuilder.h"
#include "concolic/traceclassifier.h"
#include "concolic/traceprinter.h"

namespace artemis
{



class DemoModeMainWindow : public QMainWindow
{
    Q_OBJECT

public:
    DemoModeMainWindow(WebKitExecutor *webkitExecutor, const QUrl& url);
    ~DemoModeMainWindow();

    void run(const QUrl &url);

protected:
    void closeEvent(QCloseEvent *);

private:
    // Artemis
    ArtemisWebViewPtr mWebView;
    WebKitExecutor* mWebkitExecutor;

    // GUI
    // QWidgets are owned by their parent widget and so should not be QSharedPointer.
    // TODO: so we probably should also not be storing most of these here... only the ones we access directly later.
    QWidget* mCentralWidget;
    QWidget* mArtemisWidget;
    QWidget* mAnalysisWidget;
    QLayout* mLayout;
    QLayout* mArtemisLayout;
    QVBoxLayout* mAnalysisLayout;
    QToolBar* mToolBar;
    QLineEdit* mAddressBar;
    QProgressBar* mProgressBar;
    QStatusBar* mStatusBar;
    QListWidget* mEntryPointList;
    QPushButton* mStartTraceRecordingBtn;
    QPushButton* mEndTraceRecordingBtn;
    QLabel* mTraceRecordingProgress;
    QLabel* mTraceClassificationResult;

    // The initial analysis panel is provided as its own widget.
    InitialAnalysisWidget* mInitialAnalysis;

    // The artemis browser widget.
    ArtemisBrowserWidget* mArtemisBrowser;

    void addEntryPoint(QString name, const DOMElementDescriptor* element);
    void highlightDomElement(const DOMElementDescriptor* element);
    void unHighlightDomElement(const DOMElementDescriptor* element);

    // The analysis logic itself.
    bool mWaitingForInitialLoad;
    TraceBuilderPtr mTraceBuilder;
    EntryPointDetector mEntryPointDetector;
    TraceClassifier mTraceClassifier;

    void preTraceExecution(ExecutionResultPtr result);
    void postTraceExecution();

    // The analysis/GUI interaction
    typedef QPair<QString, const DOMElementDescriptor*> EntryPointInfo;
    QList<EntryPointInfo > mKnownEntryPoints;


protected slots:
    // For the GUI.
    void slChangeLocation();
    void slAdjustLocation();
    void slLoadStarted();
    void slLoadFinished(bool ok);
    void slSetProgress(int p);

    // For the analysis logic.
    void slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result);

    // For the analysis/GUI interaction.
    void slEntryPointSelectionChanged();

    void slStartTraceRecording();
    void slEndTraceRecording();

signals:
    void sigClose();
};


typedef QSharedPointer<DemoModeMainWindow> DemoModeMainWindowPtr;

} // namespace artemis

#endif // DEMOWINDOW_H
