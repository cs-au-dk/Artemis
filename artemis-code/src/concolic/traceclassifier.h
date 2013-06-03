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

#ifndef TRACECLASSIFIER_H
#define TRACECLASSIFIER_H

#include "trace.h"
#include "tracevisitor.h"


namespace artemis
{





/*
 *  Classifies a complete annotated trace as either a success or a failure.
 *  TODO: Also modifies the trace to include an END-SUCCESS or END-FAILURE marker.
 */
class TraceClassifier : public TraceVisitor
{
public:
    TraceClassifier();

    bool classify(TraceNodePtr trace);
    bool mWasAlert;


    // Annotation nodes are used in the classification
    virtual void visit(TraceAlert* node);
    virtual void visit(TraceDomModification* node);
    virtual void visit(TracePageLoad* node);

    // Catch-all. Should not be called.
    virtual void visit(TraceNode* node);

    // Ignored for classification.
    virtual void visit(TraceBranch* node);

    // Should not be encountered on the main trace.
    virtual void visit(TraceUnexplored* node);

    // Traces should end with TraceEndUnknown nodes when they come from the trace builder.
    virtual void visit(TraceEndUnknown* node);

    // Catch-all for other end types (i.e. an error).
    virtual void visit(TraceEnd* node);
};






} // namespace artemis

#endif // TRACECLASSIFIER_H
