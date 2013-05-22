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
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(slLoadFinished(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));

    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());
    mWebView->resize(1024,768);

    QObject::connect(mWebView.data(), SIGNAL(sigClose()),
                     this, SLOT(slWebViewClosed()));
}

void ManualRuntime::run(const QUrl& url)
{
   ExecutableConfigurationPtr initial =
        ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), url));

    Log::info("CONCOLIC-INFO: Beginning initial page load...");
    mWaitingForInitialLoad = true;
    mWebkitExecutor->executeSequence(initial, true); // Calls slLoadFinished method as callback.
    //mWebView->show(); // Not shown until the analysis is done (prevents the user from interfering...).
}


// Called when a page load is complete.
void ManualRuntime::slLoadFinished(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // The sequence we are currently running has finished.
    Log::info("CONCOLIC-INFO: Finished page load");
    if(mWaitingForInitialLoad){
        mWaitingForInitialLoad = false;
        preTraceExecution();
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
void ManualRuntime::preTraceExecution()
{
    // Begin recording trace events.
    mTraceBuilder.beginRecording();

    // Simply run the entry-point detector and print out its results.
    Log::info("CONCOLIC-INFO: Analysing page entrypoints...");

    QList<EntryPoint> allEntryPoints;

    // Detect all potential entry points on the page.
    allEntryPoints = mEntryPointDetector.detectAll();

    // List them all
    foreach(EntryPoint ep, allEntryPoints){
        Log::info(QString("CONCOLIC-INFO: Potential entry point :: %1").arg(ep.name).toStdString());
    }

    // Display the page for the user to interact with.
    mWebView->show();
}


// Analyses the overall trace received from the execution.
void ManualRuntime::postTraceExecution()
{
    Log::info("CONCOLIC-INFO: Analysing trace...");
    mTraceBuilder.endRecording();

    Trace trace = mTraceBuilder.trace();

    TraceClassificationResult result = mTraceClassifier.classify(trace);

    if(result.successful){
        Log::info("CONCOLIC-INFO: This trace was classified as a SUCCESS.");
    }else{
        Log::info("CONCOLIC-INFO: This trace was classified as a FAILURE (did not submit a form).");
    }

}


} // namespace artemis
