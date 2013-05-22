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

#include "concolicdemoruntime.h"

#include "util/loggingutil.h"

namespace artemis
{


ConcolicDemoRuntime::ConcolicDemoRuntime(QObject* parent, const Options& options, const QUrl& url) :
    ManualRuntime(parent, options, url),
    waitingForFirstLoad(false)
{

}



void ConcolicDemoRuntime::run(const QUrl& url)
{
    // To begin, all we do is load the page and then wait until it is over.
    waitingForFirstLoad = true;

    // Call the parent class run() method to load the page.
    // TODO

    // Maybe warn the user not to do anything until we are ready?
    // TODO: would it be possible to block this?
}



// This is run when the page is loaded and does the initial analysis of the page.
void ConcolicDemoRuntime::concolicSetup()
{
    // Run the entry point finder.

    // Done

    // Maybe let the user know we are ready to start recording a trace, so they can start doing stuff.
}





// Slot which is notified when the page is fully loaded.
void ConcolicDemoRuntime::slPageLoadComplete()
{
    if(!waitingForFirstLoad){
        Log::error("Recieved load event when we were not waiting for it!");
        exit(1); // TODO: in reality, we probably just want to ignore this case, as it will not be an error.
    }

    waitingForFirstLoad = false;
    concolicSetup();
}



} // namespace artemis

