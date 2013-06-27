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

    // TODO: add the end marker into the trace.

    return !mWasAlert;
}









/* Definitions the visitor part **********************************************/



void TraceClassifier::visit(TraceAlert *node)
{
    mWasAlert = true;
    node->next->accept(this);
}

void TraceClassifier::visit(TraceDomModification *node)
{
    node->next->accept(this);
}

void TraceClassifier::visit(TracePageLoad *node)
{
    node->next->accept(this);
}

void TraceClassifier::visit(TraceFunctionCall *node)
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
    // We expect one branch to be "capped" by an immediate TraceUnexplored and the other to be the successor.
    // Anything else is an error (should not be present in a single trace direct from the trace builder).

    if(isImmediatelyUnexplored(node->getFalseBranch())){
        // Took 'true' branch.
        node->getTrueBranch()->accept(this);
    } else if(isImmediatelyUnexplored(node->getTrueBranch())){
        // Took 'false' branch.
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
}

void TraceClassifier::visit(TraceEndUnknown *node)
{
    // Reached the end of the trace, so stop.
}

void TraceClassifier::visit(TraceEnd *node)
{
    Log::fatal("Trace Classifier: classifying a trace which has already been classified.");
    exit(1);
}






} // namespace artemis
