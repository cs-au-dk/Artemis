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

#include "tracebuilder.h"
#include "traceeventdetectors.h"

#include "util/loggingutil.h"

namespace artemis
{

TraceBuilder::TraceBuilder(QObject* parent) :
    QObject(parent),
    mRecording(false)
{
}

void TraceBuilder::addDetector(QSharedPointer<TraceEventDetector> detector)
{
    mDetectors.append(detector);
    detector->setTraceBuilder(this);
}

void TraceBuilder::beginRecording()
{
    if(mRecording){
        Log::fatal("TraceRecorder: Began recording during an existing recording.");
        exit(1);
    }

    mRecording = true;

    // Reset the trace to be empty.
    mTrace = QSharedPointer<TraceNode>();
    mSuccessor = &mTrace;

}

void TraceBuilder::endRecording()
{
    if(!mRecording){
        return;
    }

    mRecording = false;

    // Finish off the trace with an EndUnknown node.
    *mSuccessor = QSharedPointer<TraceNode>(new TraceEndUnknown());
    mSuccessor = NULL;

}

void TraceBuilder::newNode(QSharedPointer<TraceNode> node, QSharedPointer<TraceNode>* successor)
{
    // ignore the new node unless we are recording a trace.
    if(mRecording){

        // Add the new node to the current successor pointer.
        *mSuccessor = node;

        // Update the new successor pointer
        mSuccessor = successor;

        // Notify the GUI (or anyone else) of the new node)
        emit sigAddedNode();
    }
}

TraceNodePtr TraceBuilder::trace()
{
    if(mRecording){
        Log::fatal("TraceRecorder: Requested trace during recording.");
        exit(1);
    }

    return mTrace;
}


} // namespace artemis
