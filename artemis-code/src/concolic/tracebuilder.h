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

#ifndef TRACEBUILDER_H
#define TRACEBUILDER_H

#include <QList>
#include <QSharedPointer>

#include "trace.h"


namespace artemis
{

class TraceEventDetector;

/*
 *  Records a trace of the entire execution along a single path.
 */

class TraceBuilder
{
public:
    TraceBuilder();

    //void addDetector(QSharedPointer<TraceEventDetector> detector);

    //void beginRecording();
    //void endRecording();
    //TraceNodePtr trace();

    // Called by the detectors to add a new node to the trace.
    // 'successor' must be a pointer to the 'next' 'branchTrue', 'branchFalse', etc. member of that node,
    // which will itself be null.
    //void newNode(QSharedPointer<TraceNode> node, QSharedPointer<TraceNode>* successor);

private:
    //bool mRecording; // Whether we are currently recording a trace.

    //TraceNodePtr mTrace; // The current trace.
    //QSharedPointer<TraceNode>* mSuccessor; // Where in the trace to add the next node.
    // Can't be QSharedPointer<QSharedPointer<TraceNode>> otherwise it would delete the pointed-to values too early.
    // It should be valid whenever mRecording is true.

    //QList<QSharedPointer<TraceEventDetector> > mDetectors; // The interesting event detectors which add nodes to the traces.

};


typedef QSharedPointer<TraceBuilder> TraceBuilderPtr;


} // namespace artemis





#endif // TRACEBUILDER_H
