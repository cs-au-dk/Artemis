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
    mNumAlerts = 0;
    mNumFunctionCalls = 0;

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

// For trace ends, simply end as we have nowhere to go.
void TraceStatistics::visit(TraceEnd *node)
{
    mNumNodes++;
}

void TraceStatistics::visit(TraceUnexplored *node)
{
    mNumNodes++;
}

// For concrete branch nodes, search both children and add to branch counter.
void TraceStatistics::visit(TraceConcreteBranch *node)
{
    mNumNodes++;
    mNumBranches++;
    node->getFalseBranch()->accept(this);
    node->getTrueBranch()->accept(this);
}

// For symbolic branch nodes, search both children and add to branch and symbolic counter.
void TraceStatistics::visit(TraceSymbolicBranch *node)
{
    mNumNodes++;
    mNumBranches++;
    mNumSymBranches++;
    node->getFalseBranch()->accept(this);
    node->getTrueBranch()->accept(this);
}

// Add to alert counter and continue.
void TraceStatistics::visit(TraceAlert *node)
{
    mNumNodes++;
    mNumAlerts++;
    node->next->accept(this);
}

// Add to function call counter and continue.
void TraceStatistics::visit(TraceFunctionCall *node)
{
    mNumNodes++;
    mNumFunctionCalls++;
    node->next->accept(this);
}




} // namespace artemis
