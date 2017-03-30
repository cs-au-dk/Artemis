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


#ifndef DEMOWINDOW_H
#define DEMOWINDOW_H



#include <QtGui>
#include <QLineEdit>
#include <QSharedPointer>
#include <QUrl>
#include <QList>
#include <QPair>
#include <QDir>
#include <QDesktopServices>
#include <QProcess>

#include "runtime/browser/artemiswebview.h"
#include "runtime/browser/artemiswebpage.h"
#include "runtime/browser/webkitexecutor.h"
#include "artemisbrowserwidget.h"
#include "initialanalysiswidget.h"
#include "artemisglobals.h"
#include "model/coverage/coveragetooutputstream.h"

#include "concolic/entrypoints.h"
#include "concolic/executiontree/tracenodes.h"
#include "concolic/traceclassifier.h"
#include "concolic/executiontree/traceprinter.h"
#include "concolic/tracestatistics.h"
#include "concolic/executiontree/tracedisplay.h"

#include "traceviewerdialog.h"


namespace artemis
{



class DemoModeMainWindow : public QMainWindow
{
    Q_OBJECT

public:
    DemoModeMainWindow(AppModelPtr appModel, WebKitExecutor *webkitExecutor, const QUrl& url);
    ~DemoModeMainWindow();

    void run(const QUrl &url);

protected:
    void closeEvent(QCloseEvent *);

private:
    // Artemis
    AppModelPtr mAppModel;
    ArtemisWebViewPtr mWebView;
    ArtemisWebPagePtr mWebPage;
    WebKitExecutor* mWebkitExecutor;

    // GUI
    // QWidgets are owned by their parent widget and so should not be QSharedPointer.
    // TODO: so we probably should also not be storing most of these here... only the ones we access directly later.
    QMenuBar* mMenuBar;
    QWidget* mCentralWidget;
    QWidget* mArtemisWidget;
    QWidget* mAnalysisWidget;
    QLayout* mLayout;
    QLayout* mArtemisLayout;
    QVBoxLayout* mAnalysisLayout;
    QToolBar* mToolBar;
    QLineEdit* mAddressBar;
    QProgressBar* mProgressBar;
    QPushButton* mExamplesButton;
    QStatusBar* mStatusBar;
    QLabel* mEntryPointLabel;
    QListWidget* mEntryPointList;
    QPushButton* mStartTraceRecordingBtn;
    QPushButton* mEndTraceRecordingBtn;
    QLabel* mTraceRecordingProgress;
    QLabel* mTraceClassificationResult;
    QPushButton* mViewTraceBtn;
    QPushButton* mGenerateTraceGraphButton;
    QLabel* mTraceAnalysisText;
    QPushButton* mGenerateReportsBtn;
    QPushButton* mPathTraceReportBtn;
    QPushButton* mCoverageReportBtn;
    QPushButton* mManualEntryPointXPathBtn;
    QPushButton* mManualEntryPointClickBtn;
    QLabel* mManualEntryPointDescription;

    // The initial analysis panel is provided as its own widget.
    InitialAnalysisWidget* mInitialAnalysis;

    // The artemis browser widget.
    ArtemisBrowserWidget* mArtemisBrowser;

    void addEntryPoint(QString name, DOMElementDescriptorConstPtr element);
    void highlightDomElement(DOMElementDescriptorConstPtr element);
    void unHighlightDomElement(DOMElementDescriptorConstPtr element);

    // The analysis logic itself.
    EntryPointDetector mEntryPointDetector;
    TraceClassifier mTraceClassifier;
    TraceNodePtr mPreviousTrace;

    void preTraceExecution(ExecutionResultPtr result);
    void postTraceExecution();

    // The analysis/GUI interaction
    typedef QPair<QString, DOMElementDescriptorConstPtr> EntryPointInfo;
    QList<EntryPointInfo > mKnownEntryPoints;
    int mTraceNodesRecorded;

    void displayTraceInformation();

    // Utility methods
    void loadUrl(QUrl url);
    void resetPageAnlaysis();

    // Trace and Coverage report names.
    QString mPathTraceFilename;
    QString mCoverageFilename;

    // Location of the manual entry point.
    QString mManualEntryPointXPath;
    QWebElementCollection mManualEntryPointMatches;
    QWebElement mManualEntryPointElement;
    QPoint mManualEntryPointCoordinates;


protected slots:
    // For the GUI.
    void slChangeLocation();
    void slAdjustLocation();
    void slLoadStarted();
    void slLoadFinished(bool ok);
    void slSetProgress(int p);
    void slUrlChanged(const QUrl & url);
    void slViewTrace();
    void slGenerateTraceGraph();
    void slAboutDialog();
    void slLinkHovered(const QString & link, const QString & title, const QString & textContent);
    void slJavascriptAlert(QWebFrame* frame, QString message);
    void slShowExamples();
    void slDumpDOM();

    // For the analysis logic.
    void slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result);
    void slNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, QWebPage::NavigationType type);

    // For the analysis/GUI interaction.
    void slEntryPointSelectionChanged();

    // Trace recording
    void slStartTraceRecording();
    void slEndTraceRecording();
    void slAddedTraceNode();

    // Links to coverage and trace reports
    void slShowTraceReport();
    void slShowCoverageReport();
    void slExportLinkedReports();

    // Manual entry-point selection.
    void slEnterManualEntryPoint();
    void slClickManualEntryPoint();

signals:
    void sigClose();
};


typedef QSharedPointer<DemoModeMainWindow> DemoModeMainWindowPtr;

} // namespace artemis

#endif // DEMOWINDOW_H
