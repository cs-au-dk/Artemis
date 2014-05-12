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


#include "tracestatistics.h"
#include "util/loggingutil.h"

namespace artemis
{


TraceStatistics::TraceStatistics()
{
}


// Called to run the visitor part and set the variables giving the statistics.
void TraceStatistics::processTrace(TraceNodePtr trace)
{
    // Initialise the statistic variables.
    mNumNodes = 0;

    mNumBranches = 0;
    mNumSymBranches = 0;
    mNumConcreteBranches = 0;
    mNumBranchesFullyExplored = 0;
    mNumSymBranchesFullyExplored = 0;
    mNumConcreteBranchesFullyExplored = 0;

    mNumEventSequenceSymBranches = 0;
    mNumEventSequenceSymBranchesFullyExplored = 0;

    mNumSymBranchesSinceLastMarker = 0;
    mNumSymBranchesFullyExploredSinceLastMarker = 0;

    mNumAlerts = 0;
    mNumFunctionCalls = 0;
    mNumDomModifications = 0;
    mNumInterestingDomModifications = 0;
    mNumPageLoads = 0;
    mNumEventMarkers = 0;

    mNumEndSuccess = 0;
    mNumEndFailure = 0;
    mNumEndUnknown = 0;

    mNumUnexplored = 0;
    mNumUnexploredSymbolicChild = 0;
    mNumUnexploredUnsat = 0;
    mNumUnexploredMissed = 0;
    mNumUnexploredUnsolvable = 0;

    // Run the visitor
    trace->accept(this);
}


/*
 *  The visitor part of this class.
 */

// We cover all ther cases below so this should never be called.
void TraceStatistics::visit(TraceNode *node)
{
    Log::fatal("Getting statistics for a trace node of an unknown type.");
    exit(1);
}

// For unhandled annotation types, simply continue the visiting.
void TraceStatistics::visit(TraceAnnotation *node)
{
    mNumNodes++;
    node->next->accept(this);
}

void TraceStatistics::visit(TraceConcreteBranch *node)
{
    mNumNodes++;
    mNumBranches++;
    mNumConcreteBranches++;

    if(isFullyExplored(node)) {
        mNumBranchesFullyExplored++;
        mNumConcreteBranchesFullyExplored++;
    }

    node->getFalseBranch()->accept(this);
    node->getTrueBranch()->accept(this);
}

void TraceStatistics::visit(TraceSymbolicBranch *node)
{
    mNumNodes++;
    mNumBranches++;
    mNumSymBranches++;
    mNumSymBranchesSinceLastMarker++;

    if(isFullyExplored(node)) {
        mNumBranchesFullyExplored++;
        mNumSymBranchesFullyExplored++;
        mNumSymBranchesFullyExploredSinceLastMarker++;
    }

    if(isImmediatelyUnexplored(node->getFalseBranch())) {
        mNumUnexploredSymbolicChild++;
    }

    if(isImmediatelyUnexplored(node->getTrueBranch())) {
        mNumUnexploredSymbolicChild++;
    }

    node->getFalseBranch()->accept(this);
    node->getTrueBranch()->accept(this);
}

void TraceStatistics::visit(TraceAlert *node)
{
    mNumNodes++;
    mNumAlerts++;
    node->next->accept(this);
}

void TraceStatistics::visit(TraceFunctionCall *node)
{
    mNumNodes++;
    mNumFunctionCalls++;
    node->next->accept(this);
}

void TraceStatistics::visit(TraceDomModification *node)
{
    // We only count DOM modifications if they contain any of our "indicator words".
    mNumNodes++;
    mNumDomModifications++;
    if(node->words.size() > 0) {
        mNumInterestingDomModifications++;
    }
    node->next->accept(this);
}

void TraceStatistics::visit(TracePageLoad *node)
{
    mNumNodes++;
    mNumPageLoads++;
    node->next->accept(this);
}

void TraceStatistics::visit(TraceMarker *node)
{
    mNumNodes++;
    mNumEventMarkers++;

    mNumEventSequenceSymBranches += mNumSymBranchesSinceLastMarker;
    mNumEventSequenceSymBranchesFullyExplored += mNumSymBranchesFullyExploredSinceLastMarker;

    mNumSymBranchesSinceLastMarker = 0;
    mNumSymBranchesFullyExploredSinceLastMarker = 0;

    node->next->accept(this);
}

void TraceStatistics::visit(TraceConcreteSummarisation *node)
{
    int functions = node->numFunctions();
    int branches = node ->numBranches();

    mNumNodes += functions + branches;
    mNumFunctionCalls += functions;
    mNumConcreteBranches += branches;
    // Concrete branches in a summary node cannot be fully explored.
}

void TraceStatistics::visit(TraceEndSuccess *node)
{
    mNumNodes++;
    mNumEndSuccess++;
}

void TraceStatistics::visit(TraceEndFailure *node)
{
    mNumNodes++;
    mNumEndFailure++;
}

void TraceStatistics::visit(TraceEndUnknown*node)
{
    mNumNodes++;
    mNumEndUnknown++;
}

void TraceStatistics::visit(TraceUnexplored *node)
{
    mNumNodes++;
    mNumUnexplored++;
}

void TraceStatistics::visit(TraceUnexploredUnsat *node)
{
    mNumNodes++;
    mNumUnexploredUnsat++;
}

void TraceStatistics::visit(TraceUnexploredMissed *node)
{
    mNumNodes++;
    mNumUnexploredMissed++;
}

void TraceStatistics::visit(TraceUnexploredUnsolvable *node)
{
    mNumNodes++;
    mNumUnexploredUnsolvable++;
}




// Checks if a branch is fully explored.
bool TraceStatistics::isFullyExplored(TraceBranch *node)
{
    bool leftExplored = !isImmediatelyUnexplored(node->getFalseBranch()) || isImmediatelyUnsat(node->getFalseBranch());
    bool rightExplored = !isImmediatelyUnexplored(node->getTrueBranch()) || isImmediatelyUnsat(node->getTrueBranch());;
    return leftExplored && rightExplored;
}




} // namespace artemis
