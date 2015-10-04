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


#include "traceclassifier.h"

#include "util/loggingutil.h"


namespace artemis
{



TraceClassifier::TraceClassifier()
{
}

TraceClassificationResult TraceClassifier::classify(TraceNodePtr& trace)
{
    // Simple implementation which will not be general enough for all sites.
    // Scan the trace and classify according to the following rules:
    //     * Alert -> failure
    //     * New page load -> success
    //     * DOM modification which introduces indicator words -> failure
    //     * Otherwise unknown

    trace->accept(this);

    return mResult; // Set by the visitor before returning.
}









// Definitions for the visitor part



void TraceClassifier::visit(TraceAlert *node)
{
    mResult = FAILURE;

    // Add the failure marker immediately here, and do not scan any more of the trace.
    QSharedPointer<TraceEndFailure> marker = QSharedPointer<TraceEndFailure>(new TraceEndFailure());
    marker->next = node->next;
    node->next = marker;
}

void TraceClassifier::visit(TraceDomModification *node)
{
    // Check if there are any "indicator words" in this modification.
    if(node->words.size() > 0) {
        mResult = FAILURE;

        // Add a failure marker immediately after this node, and do not continue scanning.
        QSharedPointer<TraceEndFailure> marker = QSharedPointer<TraceEndFailure>(new TraceEndFailure());
        marker->next = node->next;
        node->next = marker;

    }else{
        // If this modifcation is OK, then continue scanning the trace.
        node->next->accept(this);
    }
}

void TraceClassifier::visit(TracePageLoad *node)
{
    // We consider any page load (or POST request, etc.) as a success for getting through the *client-side* validation.
    mResult = SUCCESS;

    // Add a success marker and do not continue scanning.
    QSharedPointer<TraceEndSuccess> marker = QSharedPointer<TraceEndSuccess>(new TraceEndSuccess());
    marker->next = node->next;
    node->next = marker;
}

void TraceClassifier::visit(TraceMarker *node)
{
    node->next->accept(this);
}

void TraceClassifier::visit(TraceFunctionCall *node)
{
    node->next->accept(this);
}

void TraceClassifier::visit(TraceDivergence* node)
{
    node->next->accept(this);
}

void TraceClassifier::visit(TraceNode *node)
{
    Log::fatal("Trace Classifier: visited a node which was not handled correctly.");
    exit(1);
}

void TraceClassifier::visit(TraceBranch *node)
{
    node->getTrueBranch()->accept(this);
    node->getFalseBranch()->accept(this);
}

void TraceClassifier::visit(TraceConcreteSummarisation *node)
{
    foreach(TraceConcreteSummarisation::SingleExecution execution, node->executions) {
        execution.second->accept(this);
    }
}

void TraceClassifier::visit(TraceUnexplored *node)
{
    return;
}

void TraceClassifier::visit(TraceEndUnknown *node)
{
    // Reached the end of the trace, so stop.
    // In this simple classifier, we don't know if this is a success or failure.

    mResult = UNKNOWN;
}

void TraceClassifier::visit(TraceEnd *node)
{
    Log::fatal("Trace Classifier: classifying a trace which has already been classified.");
    exit(1);
}






} // namespace artemis
