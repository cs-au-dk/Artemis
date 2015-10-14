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

#include "tracevisitor.h"
#include "concolic/executiontree/tracenodes.h"

namespace artemis
{

// These "default" implementations simply relay the call top the parent class' method.
// They can be overriden as required to create a visitor of any granularity.
void TraceVisitor::visit(TraceUnexplored* node)         { visit(static_cast<TraceNode*>(node)); }
void TraceVisitor::visit(TraceUnexploredUnsat *node)    { visit(static_cast<TraceUnexplored*>(node)); }
void TraceVisitor::visit(TraceUnexploredUnsolvable *node){visit(static_cast<TraceUnexplored*>(node)); }
void TraceVisitor::visit(TraceUnexploredMissed *node)   { visit(static_cast<TraceUnexplored*>(node)); }
void TraceVisitor::visit(TraceUnexploredQueued *node)   { visit(static_cast<TraceUnexplored*>(node)); }

void TraceVisitor::visit(TraceBranch* node)             { visit(static_cast<TraceNode*>(node)); }
void TraceVisitor::visit(TraceConcreteBranch* node)     { visit(static_cast<TraceBranch*>(node)); }
void TraceVisitor::visit(TraceSymbolicBranch* node)     { visit(static_cast<TraceBranch*>(node)); }

void TraceVisitor::visit(TraceAnnotation* node)         { visit(static_cast<TraceNode*>(node)); }
void TraceVisitor::visit(TraceAlert* node)              { visit(static_cast<TraceAnnotation*>(node)); }
void TraceVisitor::visit(TraceDomModification* node)    { visit(static_cast<TraceAnnotation*>(node)); }
void TraceVisitor::visit(TracePageLoad* node)           { visit(static_cast<TraceAnnotation*>(node)); }
void TraceVisitor::visit(TraceMarker *node)             { visit(static_cast<TraceAnnotation*>(node));  }
void TraceVisitor::visit(TraceFunctionCall* node)       { visit(static_cast<TraceAnnotation*>(node)); }

void TraceVisitor::visit(TraceConcreteSummarisation *node){visit(static_cast<TraceNode*>(node)); }

void TraceVisitor::visit(TraceEnd* node)                { visit(static_cast<TraceNode*>(node)); }
void TraceVisitor::visit(TraceEndSuccess* node)         { visit(static_cast<TraceEnd*>(node)); }
void TraceVisitor::visit(TraceEndFailure* node)         { visit(static_cast<TraceEnd*>(node)); }
void TraceVisitor::visit(TraceEndUnknown* node)         { visit(static_cast<TraceEnd*>(node)); }

void TraceVisitor::visit(TraceDivergence* node)         { visit(static_cast<TraceAnnotation*>(node)); }



// These helper methods can be useful for concrete visitors.

// Checks if a given sub-trace is simply a single TraceUnexplored node.
// Useful for checking the branch conditions in visitors which work on straight-line traces.
bool TraceVisitor::isImmediatelyUnexplored(QSharedPointer<TraceNode> trace)
{
    return !trace.dynamicCast<TraceUnexplored>().isNull(); // Is there a more elegant way to do this?
}

bool TraceVisitor::isImmediatelyUnsat(QSharedPointer<TraceNode> trace)
{
    return !trace.dynamicCast<TraceUnexploredUnsat>().isNull();
}

bool TraceVisitor::isImmediatelyUnsolvable(QSharedPointer<TraceNode> trace)
{
    return !trace.dynamicCast<TraceUnexploredUnsolvable>().isNull();
}

bool TraceVisitor::isImmediatelyMissed(QSharedPointer<TraceNode> trace)
{
    return !trace.dynamicCast<TraceUnexploredMissed>().isNull();
}

bool TraceVisitor::isImmediatelyQueued(QSharedPointer<TraceNode> trace)
{
    return !trace.dynamicCast<TraceUnexploredQueued>().isNull();
}

bool TraceVisitor::isImmediatelyNotAttempted(QSharedPointer<TraceNode> trace)
{
    return isImmediatelyUnexplored(trace) &&
            !isImmediatelyUnsat(trace) &&
            !isImmediatelyUnsolvable(trace) &&
            !isImmediatelyMissed(trace) &&
            !isImmediatelyQueued(trace);
}


} // namespace artemis


