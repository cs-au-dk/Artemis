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

#include <assert.h>

#include <QList>

#include "concolic.h"
#include "util/loggingutil.h"

namespace artemis
{



ConcolicAnalysis::ConcolicAnalysis(bool demoMode) :
    mDemoMode(demoMode)
{
    if(!demoMode){
        Log::fatal("CONCOLIC :: Running the concolic execution in automatic mode is not supported!");
        exit(1);
    }
}

// Run the concolic execution
void ConcolicAnalysis::run()
{
    //QList<EntryPoint> allEntryPoints;

    if(mDemoMode){
        Log::info("CONCOLIC :: Running the concolic execution in demo mode.");
        // Do not perform the concolic execution but instead simply print out the relevant information.
        // (e.g. the entry-points identified, the annotated trace executed and its classification)

        // Must wait until page is loaded...
        // TODO: HOW??

        // Detect all potential entry points on the page.
        //allEntryPoints = mEntryPointDetector.detectAll(); // Signature for detectAll has changed...

        // List them all
        //foreach(EntryPoint ep, allEntryPoints){
        //    Log::info(QString("CONCOLIC :: Potential entry point :: %1").arg(ep.name).toStdString());
        //}


    }else{
        Log::info("CONCOLIC :: Running the concolic execution in automatic mode.");
        // Run the full concolic execution algorithm.

        // Not implemented.
        assert(false);
    }


}





}
