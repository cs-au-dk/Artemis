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


#include "jserrorclassifier.h"

#include "util/loggingutil.h"


namespace artemis
{

JsErrorClassifier::JsErrorClassifier()
{
}

TraceClassificationResult JsErrorClassifier::classify(TraceNodePtr &trace)
{
    trace->accept(this);
    return mResult; // Set by the visitor before returning.
}

void JsErrorClassifier::visit(TraceNode *)
{
    Log::fatal("Trace Classifier: visited a node which was not handled correctly.");
    exit(1);
}

void JsErrorClassifier::visit(TraceAlert *node)
{
    // Alerts are OK because they are part of the UI - not an "internal" error message.
    node->next->accept(this);
}

void JsErrorClassifier::visit(TraceConsoleMessage *node)
{
    // TODO: At the moment we have no way to differentiate log/info/warn/error, so treat them all as errors.
    mResult = FAILURE;

    // Add the failure marker immediately here, and do not scan any more of the trace.
    QSharedPointer<TraceEndFailure> marker = QSharedPointer<TraceEndFailure>(new TraceEndFailure());
    marker->next = node->next;
    node->next = marker;
}

void JsErrorClassifier::visit(TraceAnnotation *node)
{
    node->next->accept(this);
}

void JsErrorClassifier::visit(TraceBranch *node)
{
    node->getTrueBranch()->accept(this);
    node->getFalseBranch()->accept(this);
}

void JsErrorClassifier::visit(TraceConcreteSummarisation *node)
{
    foreach(TraceConcreteSummarisation::SingleExecution execution, node->executions) {
        execution.second->accept(this);
    }
}

void JsErrorClassifier::visit(TraceUnexplored *node)
{
    return;
}

void JsErrorClassifier::visit(TraceEndUnknown *node)
{
    // Reached the end of the trace, so stop.
    // In this simple classifier, we don't know if this is a success or failure.

    mResult = UNKNOWN;
}

void JsErrorClassifier::visit(TraceEnd *node)
{
    Log::fatal("Trace Classifier: classifying a trace which has already been classified.");
    exit(1);
}



} //namespace artemis
