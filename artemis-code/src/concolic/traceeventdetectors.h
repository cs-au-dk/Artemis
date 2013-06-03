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

#include <QString>
#include <QWebFrame>
#include <QSharedPointer>

#include "trace.h"

#ifndef TRACEEVENTDETECTORS_H
#define TRACEEVENTDETECTORS_H


namespace artemis
{


class TraceBuilder;


// I have put all the detectors into a single file for now, as I anticipate each of them being relatively simple.



/*
 *  We have multiple types of trace event detectors which detect different "interesting events" and contribute
 *  new nodes to the trace builder.
 *  This class is extended by classes which will detect events, create trace nodes and call newNode on those nodes.
 */

class TraceEventDetector
{
    Q_OBJECT

public:
    TraceEventDetector(TraceBuilder* traceBuilder):mTraceBuilder(traceBuilder){}

private:
    TraceBuilder* mTraceBuilder; // Must use standard pointer as this is set via the 'this' pointer of the parent trace builder.

protected:
    // See TraceBuilder::newNode comment in tracebuilder.h.
    void newNode(QSharedPointer<TraceNode> node, QSharedPointer<TraceNode>* successor);
};




/*
 *  Detector for branch events.
 */
class TraceBranchDetector : public TraceEventDetector
{
public:
    TraceBranchDetector(TraceBuilder* traceBuilder):TraceEventDetector(traceBuilder){}

protected slots:
    void slBranch(); // TODO: not connected to anything!
};




/*
 *  Detector for alert() calls.
 */
class TraceAlertDetector : public TraceEventDetector
{
public:
    TraceAlertDetector(TraceBuilder* traceBuilder):TraceEventDetector(traceBuilder){}

public slots:
    void slJavascriptAlert(QWebFrame *frame, QString msg);

};



} // namespace artemis

#endif // TRACEEVENTDETECTORS_H
