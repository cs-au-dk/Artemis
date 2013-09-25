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

bool TraceClassifier::classify(TraceNodePtr trace)
{
    // First simple implementation: scan the trace looking for an alert() call.
    // If there is an alert() then the trace is a failure, otherwise a success.

    mWasAlert = false;

    trace->accept(this);

    return !mWasAlert;
}









/* Definitions the visitor part **********************************************/



void TraceClassifier::visit(TraceAlert *node)
{
    mWasAlert = true;

    // In this simple classifier, we will classify this a a failure as soon as we reach an alert.
    // So we add the "failure" marker immediately here.
    // We can also stop the visitor here as well, as there is no need to continue.

    QSharedPointer<TraceEndFailure> marker = QSharedPointer<TraceEndFailure>(new TraceEndFailure());
    marker->next = node->next;
    node->next = marker;
}

void TraceClassifier::visit(TraceDomModification *node)
{
    mPreviousLink = &node->next;
    node->next->accept(this);
}

void TraceClassifier::visit(TracePageLoad *node)
{
    mPreviousLink = &node->next;
    node->next->accept(this);
}

void TraceClassifier::visit(TraceFunctionCall *node)
{
    mPreviousLink = &node->next;
    node->next->accept(this);
}

void TraceClassifier::visit(TraceNode *node)
{
    Log::fatal("Trace Classifier: visited a node which was not handled correctly.");
    exit(1);
}

void TraceClassifier::visit(TraceBranch *node)
{
    // We expect one branch to be "capped" by an immediate TraceUnexplored and the other to be the successor.
    // Anything else is an error (should not be present in a single trace direct from the trace builder).

    if(isImmediatelyUnexplored(node->getFalseBranch())){
        // Took 'true' branch.
        mPreviousLink = &node->mBranchTrue;
        node->getTrueBranch()->accept(this);
    } else if(isImmediatelyUnexplored(node->getTrueBranch())){
        // Took 'false' branch.
        mPreviousLink = &node->mBranchFalse;
        node->getFalseBranch()->accept(this);
    } else {
        // Invalid branch node
        Log::fatal("Trace Classifier: reached an invalid branch node.");
        exit(1);
    }
}

void TraceClassifier::visit(TraceUnexplored *node)
{
    // Reached the end of the trace, so stop.
    // TODO: This should not actually be reached on any well-formed trace. The only unexplored nodes should be direct children of branches.
}

void TraceClassifier::visit(TraceEndUnknown *node)
{
    // Reached the end of the trace, so stop.
    // As we only fail on alerts, this means we have a successful trace.
    // Splice in the marker just before the end.

    QSharedPointer<TraceEndSuccess> marker = QSharedPointer<TraceEndSuccess>(new TraceEndSuccess());
    // Adds the pointer to this node as the successor to the new node.
    marker->next = *mPreviousLink;
    // Replaces the pointer to this node by the marker.
    *mPreviousLink = qSharedPointerCast<TraceNode>(marker);
}

void TraceClassifier::visit(TraceEnd *node)
{
    Log::fatal("Trace Classifier: classifying a trace which has already been classified.");
    exit(1);
}






} // namespace artemis
