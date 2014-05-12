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

#ifndef TRACEBUILDER_H
#define TRACEBUILDER_H

#include <QList>
#include <QSharedPointer>

#include "concolic/executiontree/tracenodes.h"

#include "concolic/traceeventdetectors.h"


namespace artemis
{

/*
 *  Records a trace of the entire execution along a single path.
 *
 * The trace builder can either add new nodes directly, or some can be added to a larger summary node.
 * It is up to the detectors to decide which events are suitable to be summarised and call either newNode or
 * newSummaryInfo as required.
 */

class TraceBuilder : public QObject
{
    Q_OBJECT

public:
    TraceBuilder(QObject* parent, bool shouldSummarise);

    void addDetector(QSharedPointer<TraceEventDetector> detector);

    void beginRecording();
    void endRecording();
    bool isRecording() { return mRecording; }
    TraceNodePtr trace();

    // Called by the detectors to add a new node to the trace.
    // 'successor' must be a pointer to the 'next' 'branchTrue', 'branchFalse', etc. member of that node,
    // which will itself be null.
    void newNode(QSharedPointer<TraceNode> node, QSharedPointer<TraceNode>* successor);

    // Called by the detectors to add some summarisable concrete information to the trace.
    void newSummaryInfo(TraceConcreteSummarisation::EventType info);

    bool shouldSummarise() { return mSummarise; }

private:
    bool mRecording; // Whether we are currently recording a trace.

    TraceNodePtr mTrace; // The current trace.
    QSharedPointer<TraceNode>* mSuccessor; // Where in the trace to add the next node.
    // Can't be QSharedPointer<QSharedPointer<TraceNode>> otherwise it would delete the pointed-to values too early.
    // It should be valid whenever mRecording is true.

    QList<QSharedPointer<TraceEventDetector> > mDetectors; // The interesting event detectors which add nodes to the traces.

    bool mSummarise; // Whether or not this trace builder wants the detectors to notify it about summary information.
    QList<TraceConcreteSummarisation::EventType> mCurrentSummary;
    void flushSummary();

signals:
    void sigAddedNode();
};


} // namespace artemis





#endif // TRACEBUILDER_H
