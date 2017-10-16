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

#include "concolic/executiontree/tracenodes.h"
#include "concolic/executiontree/tracevisitor.h"

#ifndef TRACESTATISTICS_H
#define TRACESTATISTICS_H

namespace artemis
{


/*
 *  Gathers statistics about a complete trace which may be helpful for analysis of that trace.
 *
 *  TODO: find a better name for this class!
 */

class TraceStatistics : public TraceVisitor
{
public:
    TraceStatistics();

    int mNumNodes;

    int mNumBranches;
    int mNumSymBranches;
    int mNumConcreteBranches;
    int mNumBranchesFullyExplored;
    int mNumSymBranchesFullyExplored;
    int mNumConcreteBranchesFullyExplored;

    int mNumDivergenceNodes;
    int mNumDivergentTraces;

    int mNumEventSequenceSymBranches;
    int mNumEventSequenceSymBranchesFullyExplored;

    int mNumAlerts;
    int mNumConsoleMessages;
    int mNumFunctionCalls;
    int mNumDomModifications;
    int mNumInterestingDomModifications;
    int mNumPageLoads;
    int mNumEventMarkers;

    int mNumEndSuccess;
    int mNumEndFailure;
    int mNumEndUnknown;

    int mNumUnexplored;
    int mNumUnexploredSymbolicChild;
    int mNumUnexploredUnsat;
    int mNumUnexploredMissed;
    int mNumUnexploredUnsolvable;
    int mNumUnexploredQueued;

    void processTrace(TraceNodePtr trace);

    // Cases we ignore or which cause an error.
    virtual void visit(TraceNode* node);
    virtual void visit(TraceAnnotation* node);

    // Cases we will implement.
    virtual void visit(TraceConcreteBranch* node);
    virtual void visit(TraceSymbolicBranch* node);

    virtual void visit(TraceAlert* node);
    virtual void visit(TraceConsoleMessage* node);
    virtual void visit(TraceFunctionCall* node);
    virtual void visit(TraceDomModification* node);
    virtual void visit(TracePageLoad* node);
    virtual void visit(TraceMarker* node);

    virtual void visit(TraceDivergence* node);
    virtual void visit(TraceConcreteSummarisation* node);

    virtual void visit(TraceEndSuccess* node);
    virtual void visit(TraceEndFailure* node);
    virtual void visit(TraceEndUnknown* node);

    virtual void visit(TraceUnexplored* node);
    virtual void visit(TraceUnexploredUnsat* node);
    virtual void visit(TraceUnexploredMissed* node);
    virtual void visit(TraceUnexploredUnsolvable* node);
    virtual void visit(TraceUnexploredQueued* node);

protected:
    bool isFullyExplored(TraceBranch* node);
    int mNumSymBranchesSinceLastMarker;
    int mNumSymBranchesFullyExploredSinceLastMarker;
};


} // namespace artemis

#endif // TRACESTATISTICS_H
