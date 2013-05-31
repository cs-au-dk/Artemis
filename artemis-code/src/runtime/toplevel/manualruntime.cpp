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

#include <QList>

#include "manualruntime.h"

#include "util/loggingutil.h"


namespace artemis
{

ManualRuntime::ManualRuntime(QObject* parent, const Options& options, const QUrl& url) :
    Runtime(parent, options, url),
    mWaitingForInitialLoad(false)
{
    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());
    mWebView->resize(1024,768);

    QObject::connect(mWebView.data(), SIGNAL(sigClose()),
                     this, SLOT(slWebViewClosed()));

    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(slLoadFinished(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));
}

void ManualRuntime::run(const QUrl& url)
{
    // TEMP... testing the trace visiting.

    Log::info("Building a simple sample trace.");

    TraceBranch a;
    a.branchFalse = QSharedPointer<TraceUnexplored>(new TraceUnexplored());

    TraceAlert b;
    b.message = "Hello, World!";
    b.next = QSharedPointer<TraceEndSuccess>(new TraceEndSuccess());

    a.branchTrue = QSharedPointer<TraceAlert>(&b);

    TraceNodePtr trace(&a);

    TraceVisitorPtr boring(new VeryBoringTracePrintingVisitor());
    TraceVisitorPtr complete(new CompleteTracePrintingVisitor());
    TraceVisitorPtr search(new SearchStylePrintingVisitor());

    Log::info("Visiting with boring printer.");
    b.accept(boring.data());

    Log::info("Visiting with complete printer.");
    b.accept(complete.data());

    Log::info("Visiting with search style printer.");
    b.accept(search.data());

    Log::info("Finished testing visitors.");
    exit(1);



    ExecutableConfigurationPtr initial =
        ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), url));

    Log::info("CONCOLIC-INFO: Beginning initial page load...");
    mWaitingForInitialLoad = true;
    mWebkitExecutor->executeSequence(initial, true); // Calls slLoadFinished method as callback.
    mWebView->show();
    mWebView->setDisabled(true); // Not enabled until the analysis is done (prevents the user from interfering...).
}


// Called when a page load is complete.
void ManualRuntime::slLoadFinished(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // The sequence we are currently running has finished.
    Log::info("CONCOLIC-INFO: Finished page load");
    if(mWaitingForInitialLoad){
        mWaitingForInitialLoad = false;
        preTraceExecution(result);
    }else{
        Log::info("CONCOLIC-INFO: Page load was not the initial load, so not analysing...");
    }
}


// Called when the GUI window is closed.
void ManualRuntime::slWebViewClosed()
{
    Log::info("CONCOLIC-INFO: Trace recording is complete.");
    postTraceExecution();
    mWebkitExecutor->detach();
    done();
}



// Performs the analysis of the initial page load and reports its results.
void ManualRuntime::preTraceExecution(ExecutionResultPtr result)
{
    // Begin recording trace events.
    mTraceBuilder.beginRecording();

    // Simply run the entry-point detector and print out its results.
    Log::info("CONCOLIC-INFO: Analysing page entrypoints...");

    QList<EventHandlerDescriptor*> allEntryPoints;

    // Detect all potential entry points on the page.
    allEntryPoints = mEntryPointDetector.detectAll(result);

    // List them all
    Log::info(QString("CONCOLIC-INFO: Found %1 potential entry points.").arg(allEntryPoints.length()).toStdString());
    foreach(EventHandlerDescriptor* ep, allEntryPoints){
        Log::info(QString("CONCOLIC-INFO: Potential entry point :: %1").arg(ep->toString()).toStdString());

        ep->domElement()->getElement(mWebkitExecutor->getPage()).setStyleProperty("outline", "10px solid green");
    }

    // Display the page for the user to interact with.
    mWebView->setEnabled(true);
}


// Analyses the overall trace received from the execution.
void ManualRuntime::postTraceExecution()
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


} // namespace artemis
