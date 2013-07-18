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


#include "demowindow.h"

#include "util/loggingutil.h"

namespace artemis
{

DemoModeMainWindow::DemoModeMainWindow(AppModelPtr appModel, WebKitExecutor* webkitExecutor, const QUrl &url) :
    mAppModel(appModel),
    mWebkitExecutor(webkitExecutor),
    mEntryPointDetector(mWebkitExecutor->getPage())
{
    Log::info("DEMO: Constructing main window.");

    // Artemis' browser.
    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());

    QObject::connect(mWebView.data(), SIGNAL(loadStarted()),
                     this, SLOT(slLoadStarted()));
    QObject::connect(mWebView.data(), SIGNAL(loadFinished(bool)),
                     this, SLOT(slLoadFinished(bool)));
    QObject::connect(mWebView.data(), SIGNAL(loadFinished(bool)),
                     this, SLOT(slAdjustLocation()));
    QObject::connect(mWebView.data(), SIGNAL(urlChanged(QUrl)),
                     this, SLOT(slUrlChanged(QUrl)));
    QObject::connect(mWebView->page(), SIGNAL(sigJavascriptAlert(QWebFrame*, QString)),
                     this, SLOT(slJavascriptAlert(QWebFrame*, QString)));

    // The address bar for artemis' browser.
    mAddressBar = new QLineEdit();
    mAddressBar->setSizePolicy(QSizePolicy::Expanding, mAddressBar->sizePolicy().verticalPolicy());
    mAddressBar->setText(url.toString());
    QObject::connect(mAddressBar, SIGNAL(returnPressed()),
                     this, SLOT(slChangeLocation()));

    // Button to take you to the index of built-in examples.
    mExamplesButton = new QPushButton("Examples");
    QObject::connect(mExamplesButton, SIGNAL(released()),
                     this, SLOT(slShowExamples()));

    // Toolbar used to control the artemis browser instance.
    mToolBar = new QToolBar();
    mToolBar->addWidget(mExamplesButton);
    mToolBar->addAction(mWebView->pageAction(QWebPage::Back));
    mToolBar->addAction(mWebView->pageAction(QWebPage::Forward));
    mToolBar->addAction(mWebView->pageAction(QWebPage::Reload));
    mToolBar->addAction(mWebView->pageAction(QWebPage::Stop));
    mToolBar->addWidget(mAddressBar);

    // Progress bar for artemis' browser.
    mProgressBar = new QProgressBar();
    mProgressBar->setRange(0,100);
    mProgressBar->setFixedWidth(100);
    slSetProgress(0);
    mToolBar->addWidget(mProgressBar);
    QObject::connect(mWebView.data(), SIGNAL(loadProgress(int)),
                     this, SLOT(slSetProgress(int)));

    // Enable the status bar.
    mStatusBar = statusBar();
    QObject::connect(mWebView->page(), SIGNAL(linkHovered(QString, QString, QString)),
                     this, SLOT(slLinkHovered(QString, QString, QString)));

    // The layout for the Artemis panel.
    mArtemisLayout = new QVBoxLayout();
    mArtemisLayout->addWidget(mToolBar);
    mArtemisLayout->addWidget(mWebView.data());
    mArtemisLayout->setContentsMargins(0,0,0,0);
    mArtemisWidget = new QWidget();
    mArtemisWidget->setLayout(mArtemisLayout);

    // Entry points list for the analysis panel.
    mEntryPointList = new QListWidget();
    mEntryPointList->setSizePolicy(QSizePolicy::Expanding, QSizePolicy::Minimum);

    // Buttons for Trace Recording panel.
    mStartTraceRecordingBtn = new QPushButton("Start Recording");
    mEndTraceRecordingBtn = new QPushButton("End Recording");
    QObject::connect(mStartTraceRecordingBtn, SIGNAL(released()),
                     this, SLOT(slStartTraceRecording()));
    QObject::connect(mEndTraceRecordingBtn, SIGNAL(released()),
                     this, SLOT(slEndTraceRecording()));
    mEndTraceRecordingBtn->setEnabled(false);

    // Button and text for trace analysis panel.
    mViewTraceBtn = new QPushButton("View Trace");
    QObject::connect(mViewTraceBtn, SIGNAL(released()),
                     this, SLOT(slViewTrace()));
    mViewTraceBtn->setEnabled(false);

    mGenerateTraceGraphButton = new QPushButton("Generate Graph");
    QObject::connect(mGenerateTraceGraphButton, SIGNAL(released()),
                     this, SLOT(slGenerateTraceGraph()));
    mGenerateTraceGraphButton->setEnabled(false);

    mTraceAnalysisText = new QLabel("No trace has been run yet.");

    // The Layout for the initial analysis panel.
    mAnalysisLayout = new QVBoxLayout();
    QLabel* analysisLabel = new QLabel("Page Analysis");
    QFont labelFont;
    labelFont.setPointSize(18);
    analysisLabel->setFont(labelFont);
    mAnalysisLayout->addSpacing(5);
    mAnalysisLayout->addWidget(analysisLabel);
    mAnalysisLayout->addSpacing(10);

    QFont sectionFont;
    sectionFont.setBold(true);

    QLabel* entryPointLabel = new QLabel("Potential Entry Points:");
    entryPointLabel->setFont(sectionFont);
    mAnalysisLayout->addWidget(entryPointLabel);
    mAnalysisLayout->addWidget(mEntryPointList);
    mAnalysisLayout->addWidget(new QLabel("Currently we only detect 'click' events on\n'button' elements and 'a' elements within\nforms.\n\nSelect an entry above to highlight it on the page."));
    mAnalysisLayout->addSpacing(10);

    QLabel* curTraceLabel = new QLabel("Trace Recording:");
    curTraceLabel->setFont(sectionFont);
    mAnalysisLayout->addWidget(curTraceLabel);
    mAnalysisLayout->addWidget(mStartTraceRecordingBtn);
    mAnalysisLayout->addWidget(mEndTraceRecordingBtn);

    mTraceRecordingProgress = new QLabel("Trace Nodes Recorded: No trace running.");
    mAnalysisLayout->addWidget(mTraceRecordingProgress);
    mAnalysisLayout->addSpacing(10);

    QLabel* traceAnalysisLabel = new QLabel("Previous Trace Analysis:");
    traceAnalysisLabel->setFont(sectionFont);
    mAnalysisLayout->addWidget(traceAnalysisLabel);
    mAnalysisLayout->addWidget(mTraceAnalysisText);

    mTraceClassificationResult = new QLabel("");
    mTraceClassificationResult->setVisible(false);
    mAnalysisLayout->addWidget(mTraceClassificationResult);

    mAnalysisLayout->addWidget(mViewTraceBtn);
    mAnalysisLayout->addWidget(mGenerateTraceGraphButton);
    mAnalysisLayout->addSpacing(10);

    // Execution reports section.
    QLabel* reportsLabel = new QLabel("Execution Reports");
    reportsLabel->setFont(sectionFont);
    QLabel* reportsExplanation = new QLabel("These reports (currently) record all trace and coverage information since the start of the session.");
    mAnalysisLayout->addWidget(reportsLabel);
    mAnalysisLayout->addWidget(reportsExplanation);
    mGenerateReportsBtn = new QPushButton("Generate Reports");
    QObject::connect(mGenerateReportsBtn, SIGNAL(released()),
                     this, SLOT(slExportLinkedReports()));
    mAnalysisLayout->addWidget(mGenerateReportsBtn);
    mPathTraceReportBtn = new QPushButton("Path Trace Report");
    QObject::connect(mPathTraceReportBtn, SIGNAL(released()),
                     this, SLOT(slShowTraceReport()));
    mPathTraceReportBtn->setDisabled(true);
    mAnalysisLayout->addWidget(mPathTraceReportBtn);
    mCoverageReportBtn = new QPushButton("Coverage Report");
    QObject::connect(mCoverageReportBtn, SIGNAL(released()),
                     this, SLOT(slShowCoverageReport()));
    mCoverageReportBtn->setDisabled(true);
    mAnalysisLayout->addWidget(mCoverageReportBtn);
    mAnalysisLayout->addSpacing(10);


    mAnalysisLayout->setContentsMargins(0,0,0,0);
    mAnalysisLayout->setAlignment(Qt::AlignTop);
    mAnalysisWidget = new QWidget();
    mAnalysisWidget->setLayout(mAnalysisLayout);
    mAnalysisWidget->setFixedWidth(300);

    // The layout for the main window.
    mLayout = new QHBoxLayout();
    mLayout->addWidget(mArtemisWidget);
    //QFrame* separatingLine = new QFrame();
    //separatingLine->setFrameShape(QFrame::VLine);
    //mLayout->addWidget(separatingLine);
    mLayout->addWidget(mAnalysisWidget);
    mLayout->setContentsMargins(0,0,11,0);
    mLayout->setSpacing(11);

    // Main window needs to have a central widget containing the main content...
    mCentralWidget = new QWidget(this);
    mCentralWidget->setLayout(mLayout);
    setCentralWidget(mCentralWidget);

    // Enable menu bar
    mMenuBar = new QMenuBar(this);

    QMenu* fileMenu = new QMenu("&File", mMenuBar);
    QAction* exitAction = fileMenu->addAction("&Exit");
    connect(exitAction, SIGNAL(triggered()), this, SLOT(close()));

    QMenu* helpMenu = new QMenu("&Help", mMenuBar);
    QAction* aboutAction = helpMenu->addAction("&About");
    connect(aboutAction, SIGNAL(triggered()), this, SLOT(slAboutDialog()));

    mMenuBar->addMenu(fileMenu);
    mMenuBar->addMenu(helpMenu);
    setMenuBar(mMenuBar);

    // Set what the window looks like
    resize(1300, 800);
    setWindowTitle("Artemis Demonstration Mode");


    // Signals used by the analysis itself.
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(slExecutedSequence(ExecutableConfigurationConstPtr,QSharedPointer<ExecutionResult>)));

    // Signals used by the analysis/GUI interaction.
    QObject::connect(mEntryPointList, SIGNAL(itemSelectionChanged()),
                     this, SLOT(slEntryPointSelectionChanged()));

    QObject::connect(mWebkitExecutor->getTraceBuilder(), SIGNAL(sigAddedNode()),
                     this, SLOT(slAddedTraceNode()));


    // Configure the connection with ArtemisWebPage which allows interception of page loads.
    // TODO: the pointer from mWebViw is only to QWebPage, but we need ArtemisWebPage.
    // This cast seems a bit of a hack, but we also don't want to modify QWebPage with the extra functionality we need.
    // Maybe it would be better to modift ArtemisWebView to return ArtemisWebPage from the page() method?
    mWebPage = dynamic_cast<ArtemisWebPage*>(mWebView->page());
    if(!mWebPage){
        Log::fatal("Using an ArtemisWebView which does not use an ArtemisWebPage.");
        exit(1);
    }
    QObject::connect(mWebPage, SIGNAL(sigNavigationRequest(QWebFrame*,QNetworkRequest,QWebPage::NavigationType)),
                     this, SLOT(slNavigationRequest(QWebFrame*,QNetworkRequest,QWebPage::NavigationType)));
    mWebPage->mAcceptNavigation = false;



    // TODO: all the above is temp and needs to move into ArtemisBrowserWidget.
/*
    // The layout manager for this window.
    QHBoxLayout* layout = new QHBoxLayout();

    // Initial analysis results from artemis.
    mInitialAnalysis = new InitialAnalysisWidget(this);
    layout->addWidget(mInitialAnalysis);

    // Browser widget displaying Artemis' browser.
    mArtemisBrowser = new ArtemisBrowserWidget(this);
    layout->addWidget(mArtemisBrowser);

    // Set up this window.
    setLayout(layout);
    resize(1024, 768);
    setWindowTitle("Artemis Demonstration Mode");

    //setCentralWidget(initialAnalysis);
*/
}

DemoModeMainWindow::~DemoModeMainWindow()
{
    Log::info("DEMO: Destroying main window.");
    // Do not delete mWebkitExecutor, that is managed from elsewhere.
    // TODO: do we need to manually delete all the widget objects or are they handled automatically by their parents?
}


// Called when the window is closed.
void DemoModeMainWindow::closeEvent(QCloseEvent *)
{
    Log::info("DEMO: Window closed.");

    emit sigClose();
}


// Called when we choose a new page via the loaction bar.
void DemoModeMainWindow::slChangeLocation()
{
    Log::info(QString("DEMO: Changed loaction to %1").arg(mAddressBar->text()).toStdString());
    QUrl url = QUrl(mAddressBar->text());

    // Validate the URL (as in artemis.cpp).
    // TODO: it is not clear whether this is needed, as WebKit seems to do something similar on its own.
    if(url.scheme().isEmpty()){
        url = QUrl("http://" + url.toString());
    }

    if(url.isValid()){
        loadUrl(url);
    }else{
        QMessageBox urlError(this);
        urlError.setText("Error: The URL is invalid.");
        urlError.exec();
    }
}


// Called when we need to update the contents of the address bar.
void DemoModeMainWindow::slAdjustLocation()
{
    mAddressBar->setText(mWebView->url().toString());
    Log::info(QString("DEMO: Adjusted loaction to %1").arg(mWebView->url().toString()).toStdString());
}


// Called when we begin loading a page.
void DemoModeMainWindow::slLoadStarted()
{
    Log::info("DEMO: Begin page load.");
}

// Called when we finish loading a page.
void DemoModeMainWindow::slLoadFinished(bool ok)
{
    Log::info("DEMO: Finished page load.");
    mWebPage->mAcceptNavigation = false; // Now that we are done loading, any further navigation must be via loadUrl().
    mWebView->setEnabled(true); // Re-allow interaction with the page once it is loaded completely.
}

// Called when the page loading progress needs to be updated.
void DemoModeMainWindow::slSetProgress(int p)
{
    Log::info(QString("DEMO: Updating page load progress: %1%").arg(p).toStdString());
    mProgressBar->setValue(p);
    if(p >= 100){
        mProgressBar->setFormat("Loaded.");
    }else{
        mProgressBar->setFormat("Loading: %p%");
    }
}


// Called whenever the URL of the page changes.
void DemoModeMainWindow::slUrlChanged(const QUrl &url)
{
    Log::info(QString("DEMO: URL changed to %1").arg(url.toString()).toStdString());
}



// Called to start the analysis.
void DemoModeMainWindow::run(const QUrl& url)
{
    Log::info("CONCOLIC-INFO: Beginning initial page load...");
    loadUrl(url);
}



// Called when the webkit executor finishes running an execution sequence.
// In our case that is after any page load.
void DemoModeMainWindow::slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // The sequence we are currently running has finished.
    Log::info("CONCOLIC-INFO: Finished execution sequence.");
    preTraceExecution(result);
}


// Called when the ArtemisWebPage receives a request for navigation and we have set it's mAcceptingNavigation flag to false.
// i.e. when we want to intercept the load and pass it to WebkitExecutor instead.
void DemoModeMainWindow::slNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, QWebPage::NavigationType type)
{
    Log::info(QString("DEMO: Navigation intercepted to %1").arg(request.url().toString()).toStdString());

    loadUrl(request.url());
}



// Called to run the pre-trace analysis before ANY trace is run.
void DemoModeMainWindow::preTraceExecution(ExecutionResultPtr result)
{
    // Simply run the entry-point detector and display its results.
    Log::info("CONCOLIC-INFO: Analysing page entrypoints...");

    QList<EventHandlerDescriptor*> allEntryPoints;

    // Detect all potential entry points on the page.
    allEntryPoints = mEntryPointDetector.detectAll(result);

    // List them all
    Log::info(QString("CONCOLIC-INFO: Found %1 potential entry points.").arg(allEntryPoints.length()).toStdString());
    foreach(EventHandlerDescriptor* ep, allEntryPoints){
        // Log to termianl
        Log::info(QString("CONCOLIC-INFO: Potential entry point :: %1").arg(ep->toString()).toStdString());
        // Log to GUI.
        addEntryPoint(ep->toString(), ep->domElement());
    }

    // Display the page for the user to interact with.
    mWebView->setEnabled(true);

}

// Called once the trace recording is over (signalled by the user).
void DemoModeMainWindow::postTraceExecution()
{
    Log::info("CONCOLIC-INFO: Analysing trace...");
    mWebkitExecutor->getTraceBuilder()->endRecording();

    mPreviousTrace = mWebkitExecutor->getTraceBuilder()->trace();

    bool result = mTraceClassifier.classify(mPreviousTrace);

    mTraceClassificationResult->setVisible(true);
    if(result){
        Log::info("CONCOLIC-INFO: This trace was classified as a SUCCESS.");
        mTraceClassificationResult->setText("Classification: <font color='green'>SUCCESS</font>");
    }else{
        Log::info("CONCOLIC-INFO: This trace was classified as a FAILURE.");
        mTraceClassificationResult->setText("Classification: <font color='red'>FAILURE</font>");
    }

    // Reset the trace tracking text in the GUI.
    mTraceRecordingProgress->setText("Trace Nodes Recorded: No trace running.");

    // Generate and display some information about this trace.
    displayTraceInformation();
}


// Add some information about a trace to the GUI.
// Populates the "Trace Analysis" panel.
void DemoModeMainWindow::displayTraceInformation()
{
    mViewTraceBtn->setEnabled(true);
    mGenerateTraceGraphButton->setEnabled(true);

    TraceStatistics stats;
    stats.processTrace(mPreviousTrace);

    mTraceAnalysisText->setText(QString("Events Recorded: %1\nBranches: %2\nSymbolic Branches: %3\nAlerts: %4\nFunction Calls: %5")
                                .arg(stats.mNumNodes).arg(stats.mNumBranches).arg(stats.mNumSymBranches).arg(stats.mNumAlerts)
                                .arg(stats.mNumFunctionCalls));

    // If the trace is small enough to usefully disply, then print it in the temrinal.
    Log::info("CONCOLIC-INFO: Printout of the trace:");
    if(stats.mNumNodes < 50){
        TerminalTracePrinter printer;
        printer.printTraceTree(mPreviousTrace);
    }else{
        Log::info("CONCOLIC-INFO: Trace is too large to print to terminal.");
    }
}


// Uses the webkit executor to load a URL.
// All page loads (excluding navigations done during another load, such as fetching adverts, some redirections etc)
// should be done via this function. mWebPage->mAcceptNavigation helps to ensure this is the case.
void DemoModeMainWindow::loadUrl(QUrl url)
{
    mWebPage->mAcceptNavigation = true; // Allow navigation during load. This will be reset once the loading phase is finished.
    mWebView->setEnabled(false); // Disable interaction with the page during load.

    Log::info(QString("CONCOLIC-INFO: Loading page %1").arg(url.toString()).toStdString());
    ExecutableConfigurationPtr initial = ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), url));
    mWebkitExecutor->executeSequence(initial, true); // Calls slExecutedSequence method as callback.

    resetPageAnlaysis();
}

// Called when we load a new page to reset the entry point analysis information (in the app state and in the GUI).
void DemoModeMainWindow::resetPageAnlaysis()
{
    mKnownEntryPoints.clear();
    mEntryPointList->clear();
}



// Called to add a new potential entry point to the entry point list.
void DemoModeMainWindow::addEntryPoint(QString name, const DOMElementDescriptor* element)
{
    // First we add this entry point to the list.
    int index = mKnownEntryPoints.size();
    mKnownEntryPoints.append(EntryPointInfo(name, element));

    // Then create a QListWidgetitem with the name and store the index in the list so we can reference the element pointer later.
    QListWidgetItem* item = new QListWidgetItem();
    item->setText(name);
    item->setData(Qt::UserRole, index);

    mEntryPointList->addItem(item);

    // TODO: is it possible to resize this list widget to fit the contents?
    // Seems to be non-trivial but probably not too hard...
}


// Called whenever the selection of elements in the entry point list changes.
void DemoModeMainWindow::slEntryPointSelectionChanged()
{
    //Log::info("CONCOLIC-INFO: Entry point selection changed.");

    // Un-highlight any previously highlighted elements.
    foreach(EntryPointInfo entry, mKnownEntryPoints){
        unHighlightDomElement(entry.second);
    }

    QList<QListWidgetItem*> items = mEntryPointList->selectedItems();

    foreach(QListWidgetItem* selected, items){
        //Log::info(QString("CONCOLIC-INFO: Highlighting %1").arg(selected->text()).toStdString());
        int index = selected->data(Qt::UserRole).value<int>();
        highlightDomElement(mKnownEntryPoints.at(index).second);
    }
}


// Called to highlight a particular DOM element in the artemis web view.
void DemoModeMainWindow::highlightDomElement(const DOMElementDescriptor *element)
{
    element->getElement(mWebkitExecutor->getPage()).setStyleProperty("outline", "10px solid green");
}

void DemoModeMainWindow::unHighlightDomElement(const DOMElementDescriptor *element)
{
    element->getElement(mWebkitExecutor->getPage()).setStyleProperty("outline", "none");
    // TODO: what if it had an outline to begin with?
}



// Called when the button to start a trace recording is used.
void DemoModeMainWindow::slStartTraceRecording()
{
    Log::info("CONCOLIC-INFO: Pressed 'Start Recording' button.");
    mStartTraceRecordingBtn->setEnabled(false);
    mEndTraceRecordingBtn->setEnabled(true);

    // Begin recording trace events.
    mWebkitExecutor->getTraceBuilder()->beginRecording();

    mTraceRecordingProgress->setText("Trace Nodes Recorded: 0");
    mTraceNodesRecorded = 0;
}


// Called when the button to end a trace recording is used.
void DemoModeMainWindow::slEndTraceRecording()
{
    Log::info("CONCOLIC-INFO: Pressed 'End Recording' button.");
    mStartTraceRecordingBtn->setEnabled(true);
    mEndTraceRecordingBtn->setEnabled(false);

    // Stop recording and analyse trace events.
    postTraceExecution();
}


// Called when a new node is added by the trace builder.
void DemoModeMainWindow::slAddedTraceNode()
{
    Log::info("CONCOLIC-INFO: Added new node to trace.");

    mTraceNodesRecorded++;
    mTraceRecordingProgress->setText(QString("Trace Nodes Recorded: %1").arg(mTraceNodesRecorded));
}


// Called when the "View Trace" button is clicked.
void DemoModeMainWindow::slViewTrace()
{
    Log::info("DEMO: Viewing trace.");

    QDialog* traceViewer = new TraceViewerDialog(mPreviousTrace, this);
    traceViewer->show();
}


// Called when the "Generate Trace Graph" button is clicked.
void DemoModeMainWindow::slGenerateTraceGraph()
{
    QString graphFile, pngFile;

    Log::info("DEMO: Generating trace graph.");
    TraceDisplay display;
    display.writeGraphFile(mPreviousTrace, graphFile);

    if(graphFile.endsWith(".gv")){
        pngFile = graphFile;
        pngFile.chop(3);
        pngFile += ".png";
    }else{
        pngFile = graphFile + ".png";
    }

    // Convert to PNG
    QString command = QString("dot -Tpng %1 -o %2").arg(graphFile).arg(pngFile);
    QProcess process;
    process.start(command);

    // Display the PNG.
    process.waitForFinished(); // Blocks until the png is generated.

    // TODO: what do we do if there was any problem?
    ImageViewerDialog imageView(pngFile);
    imageView.exec();


}


// Called when Help>About is triggered.
void DemoModeMainWindow::slAboutDialog()
{
    QMessageBox::about(this, "About Artemis", "Artemis is a tool that performs automated, feedback-directed testing of JavaScript applications. <br/><br/>This demonstration mode shows off some of Artemis' symbolic features. <br/><br/>Please see the <a href='http://github.com/cs-au-dk/Artemis' >GitHub page</a> for more information.");
}


// Called when a link is hovered over in the artemis browser.
void DemoModeMainWindow::slLinkHovered(const QString & link, const QString & title, const QString & textContent)
{
    mStatusBar->showMessage(link);
}


// Called when an alert() call is made in javascript.
void DemoModeMainWindow::slJavascriptAlert(QWebFrame *frame, QString message)
{
    // TODO: might be useful to have some way to turn these off!
    QMessageBox::critical(this, "Alert", message);
}


// Called when the Examples button is pressed to display the examples index.
void DemoModeMainWindow::slShowExamples()
{
    loadUrl(examplesIndexUrl());
}



// Attached to the "View trace report" button.
// Prevented (by UI) from being called until mPathTraceFilename is set.
void DemoModeMainWindow::slShowTraceReport()
{
    bool success = QDesktopServices::openUrl(mPathTraceFilename);
    if(!success){
        QMessageBox::critical(this, "Error", "There was a problem opening the browser for viewing.");
    }
}


// Attached to the "View coverage report" button.
// Prevented (by UI) from being called until mCoverageFilename is set.
void DemoModeMainWindow::slShowCoverageReport()
{
    bool success = QDesktopServices::openUrl(mCoverageFilename);
    if(!success){
        QMessageBox::critical(this, "Error", "There was a problem opening the browser for viewing.");
    }
}


// Attached to the "Generate Reports" button.
void DemoModeMainWindow::slExportLinkedReports()
{
    // Write out the reports (and set the file names used for viewing).
    writeCoverageHtml(mAppModel->getCoverageListener(), mCoverageFilename);
    mAppModel->getPathTracer()->writePathTraceHTML(true, mCoverageFilename, mPathTraceFilename);

    // Tell the user what we have done.
    QMessageBox::about(this, "Report Export", QString("Exported the following report files:\n\n%1\n%2").arg(mPathTraceFilename).arg(mCoverageFilename));
    // TODO: Remove this once we can view the reports from within artemis.

    // Add the current working directory to these paths so they are full file:// URLs.
    // TODO: do this in a more robust way!
    mPathTraceFilename = "file://" + QDir::currentPath() + "/" + mPathTraceFilename;
    mCoverageFilename = "file://" + QDir::currentPath() + "/" + mCoverageFilename;

    // Enable the report viewing buttons now that there are reports to view.
    mPathTraceReportBtn->setEnabled(true);
    mCoverageReportBtn->setEnabled(true);
}



} // namespace artemis

