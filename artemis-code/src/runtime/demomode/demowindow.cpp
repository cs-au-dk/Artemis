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



DemoModeMainWindow::DemoModeMainWindow(WebKitExecutor* webkitExecutor, const QUrl &url) :
    mWebkitExecutor(webkitExecutor),
    mWaitingForInitialLoad(false)
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

    // The address bar for artemis' browser.
    mAddressBar = new QLineEdit();
    mAddressBar->setSizePolicy(QSizePolicy::Expanding, mAddressBar->sizePolicy().verticalPolicy());
    mAddressBar->setText(url.toString());
    QObject::connect(mAddressBar, SIGNAL(returnPressed()),
                     this, SLOT(slChangeLocation()));

    // Toolbar used to control the artemis browser instance.
    mToolBar = new QToolBar();
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

    // The layout for the Artemis panel.
    mArtemisLayout = new QVBoxLayout();
    mArtemisLayout->addWidget(mToolBar);
    mArtemisLayout->addWidget(mWebView.data());
    mArtemisLayout->setContentsMargins(0,0,0,0);
    mArtemisWidget = new QWidget();
    mArtemisWidget->setLayout(mArtemisLayout);

    // Toolbox for analysis panel.
    //QToolBox* mAnalysisToolBox = new QToolBox();
    //mAnalysisToolBox->addItem(new QPushButton("Hi There"), "Informal");
    //mAnalysisToolBox->addItem(new QPushButton("Good morning"), "Formal");

    // Entry points list for the analysis panel.
    mEntryPointList = new QListWidget();
    mEntryPointList->setSizePolicy(QSizePolicy::Expanding, QSizePolicy::Minimum);

    // The Layout for the initial analysis panel.
    mAnalysisLayout = new QVBoxLayout();
    QLabel* analysisLabel = new QLabel("Page Analysis");
    QFont labelFont;
    labelFont.setPointSize(18);
    analysisLabel->setFont(labelFont);
    mAnalysisLayout->addSpacing(5);
    mAnalysisLayout->addWidget(analysisLabel);
    //mAnalysisLayout->addWidget(new QPushButton("Hello A"));
    //mAnalysisLayout->addWidget(new QPushButton("Hello B"));
    //mAnalysisLayout->addWidget(new QPushButton("Hello C"));
    //mAnalysisLayout->addWidget(new QPushButton("Hello D"));
    //mAnalysisLayout->addWidget(mAnalysisToolBox);
    mAnalysisLayout->addSpacing(10);

    QFont sectionFont;
    sectionFont.setBold(true);

    QLabel* entryPointLabel = new QLabel("Potential Entry Points:");
    entryPointLabel->setFont(sectionFont);
    mAnalysisLayout->addWidget(entryPointLabel);
    mAnalysisLayout->addWidget(mEntryPointList);
    mAnalysisLayout->addWidget(new QLabel("Currently we only detect 'click' events on\n'button' elements."));
    mAnalysisLayout->addSpacing(10);

    QLabel* curTraceLabel = new QLabel("Current Trace:");
    curTraceLabel->setFont(sectionFont);
    mAnalysisLayout->addWidget(curTraceLabel);
    mAnalysisLayout->addWidget(new QLabel("(nothing here yet)"));
    mAnalysisLayout->addSpacing(10);

    QLabel* traceClassLabel = new QLabel("Trace Classification:");
    traceClassLabel->setFont(sectionFont);
    mAnalysisLayout->addWidget(traceClassLabel);
    mAnalysisLayout->addWidget(new QLabel("(nothing here yet)"));
    mAnalysisLayout->addSpacing(10);

    QLabel* otherInfoLabel = new QLabel("Other Info:");
    otherInfoLabel->setFont(sectionFont);
    mAnalysisLayout->addWidget(otherInfoLabel);
    mAnalysisLayout->addWidget(new QLabel("(nothing here yet)"));

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

    // Enable the status bar.
    // For now we are not puttin anything in here, but it makes it much easier to resize the window!
    mStatusBar = statusBar();

    // Set what the window looks like
    resize(1300, 800);
    setWindowTitle("Artemis Demonstration Mode");


    // Signals used by the analysis itself.
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(slExecutedSequence(ExecutableConfigurationConstPtr,QSharedPointer<ExecutionResult>)));

    // Signals used by the analysis/GUI interaction.
    QObject::connect(mEntryPointList, SIGNAL(itemSelectionChanged()),
                     this, SLOT(slEntryPointSelectionChanged()));




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
    emit sigClose();
}



// Called when we choose a new page via the loaction bar.
void DemoModeMainWindow::slChangeLocation()
{
    Log::info(QString("DEMO: Changed loaction to %1").arg(mAddressBar->text()).toStdString());
    QUrl url = QUrl(mAddressBar->text());
    mWebView->load(url);
    mWebView->setFocus();
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




// Called to start the analysis.
void DemoModeMainWindow::run(const QUrl& url)
{
    ExecutableConfigurationPtr initial =
        ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), url));

    Log::info("CONCOLIC-INFO: Beginning initial page load...");
    mWaitingForInitialLoad = true;
    mWebkitExecutor->executeSequence(initial, true); // Calls slExecutedSequence method as callback.

    mWebView->setDisabled(true); // Not enabled until the analysis is done (prevents the user from interfering...).
}



// Called when the webkit executor finishes running an execution sequence.
// In our case that is after the initial load.
void DemoModeMainWindow::slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // The sequence we are currently running has finished.
    Log::info("CONCOLIC-INFO: Finished execution sequence.");
    if(mWaitingForInitialLoad){
        mWaitingForInitialLoad = false;
        preTraceExecution(result);
    }else{
        Log::info("CONCOLIC-INFO: Page load was not the initial load, so not analysing...");
    }
}



// Called to run the pre-trace analysis and start recording a trace.
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
        // Highlight in browser window.
        //highlightDomElement(ep->domElement()); // This is now done by selecting them in the list box.
    }


    // Begin recording trace events.
    mTraceBuilder.beginRecording();

    // Display the page for the user to interact with.
    mWebView->setEnabled(true);

}

// Called once the trace recording is over (signalled by the user).
// TODO: this is never called from anywhere yet!
void DemoModeMainWindow::postTraceExecution()
{
    Log::info("CONCOLIC-INFO: Analysing trace...");
    mTraceBuilder.endRecording();

    TraceNodePtr trace = mTraceBuilder.trace();

    TraceClassificationResult result = mTraceClassifier.classify(trace);

    if(result.successful){
        Log::info("CONCOLIC-INFO: This trace was classified as a SUCCESS.");
    }else{
        Log::info("CONCOLIC-INFO: This trace was classified as a FAILURE (did not submit a form).");
    }
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






} // namespace artemis

