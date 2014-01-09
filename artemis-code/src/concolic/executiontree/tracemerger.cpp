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

#include <stdlib.h>
#include <QDebug>

#include "util/loggingutil.h"

#include "tracemerger.h"

namespace artemis
{

TraceNodePtr TraceMerger::merge(TraceNodePtr trace, TraceNodePtr executiontree)
{
    if (trace.isNull()) {
        return executiontree;
    }

    if (executiontree.isNull()) {
        return trace; // replace the entire execution tree with the trace
    }

    TraceMerger merger;

    merger.mCurrentTrace = trace;
    merger.mCurrentTree = executiontree;
    trace->accept(&merger);

    return merger.mCurrentTree;
}

void TraceMerger::visit(TraceUnexplored* node)
{
    // Ignore, we can't add any information to the execution tree
    return;
}

void TraceMerger::visit(TraceEnd* node)
{
    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        return;
    }

    // case: trace end
    if (!mCurrentTrace->isEqualShallow(mCurrentTree)) {
        qWarning() << "Warning, divergance discovered while merging a trace! (TraceEnd)";
        statistics()->accumulate("Concolic::ExecutionTree::DivergentMerges", 1);
        Log::info("  Trace merge diverged from the tree (TraceEnd).");
    }
}

void TraceMerger::visit(TraceBranch* node)
{
    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        return;
    }

    // case: traceBranch
    if (node->isEqualShallow(mCurrentTree)) {

        TraceBranchPtr treeBranch = mCurrentTree.dynamicCast<TraceBranch>();

        // Add statistics if we are completing the exploratrion of this branch.
        // i.e. if one branch is explored in the tree, and the unexplored branch is to be replaced by something else in the trace.
        if((TraceVisitor::isImmediatelyUnexplored(treeBranch->getTrueBranch())
                && !TraceVisitor::isImmediatelyUnexplored(treeBranch->getFalseBranch())
                && !TraceVisitor::isImmediatelyUnexplored(node->getTrueBranch()))
            || (TraceVisitor::isImmediatelyUnexplored(treeBranch->getFalseBranch())
                && !TraceVisitor::isImmediatelyUnexplored(treeBranch->getTrueBranch())
                && !TraceVisitor::isImmediatelyUnexplored(node->getFalseBranch()))) {
            // Check whether we are exploring a new path at this branch node.
            if(TraceVisitor::isImmediatelyConcreteBranch(treeBranch)) {
                statistics()->accumulate("Concolic::ExecutionTree::ConcreteBranchesFullyExplored", 1);
            }else{
                statistics()->accumulate("Concolic::ExecutionTree::SymbolicBranchesFullyExplored", 1);
            }
        }
        // "Fix" the statistics for branch counts
        // This is a slight hack as we count nodes multiple times in the detector but then we decrement the counter
        // again here for any duplicate nodes.
        if(TraceVisitor::isImmediatelyConcreteBranch(treeBranch)) {
            statistics()->accumulate("Concolic::ExecutionTree::ConcreteBranchesTotal", -1);
        }else{
            statistics()->accumulate("Concolic::ExecutionTree::SymbolicBranchesTotal", -1);
        }


        // Merge the traces for each branch

        mCurrentTree = treeBranch->getTrueBranch();
        mCurrentTrace = node->getTrueBranch();
        mCurrentTrace->accept(this);

        treeBranch->setTrueBranch(mCurrentTree);

        mCurrentTree = treeBranch->getFalseBranch();
        mCurrentTrace = node->getFalseBranch();
        mCurrentTrace->accept(this);

        treeBranch->setFalseBranch(mCurrentTree);

        mCurrentTree = treeBranch;
        return;
    }

    qWarning() << "Warning, divergance discovered while merging a trace! (TraceBranch)";
    statistics()->accumulate("Concolic::ExecutionTree::DivergentMerges", 1);
    Log::info("  Trace merge diverged from the tree (TraceBranch).");
}

void TraceMerger::visit(TraceAnnotation* node)
{
    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        return;
    }

    if (node->isEqualShallow(mCurrentTree)) {

        fixDoubleCountedAnnotations(mCurrentTree);

        TraceAnnotationPtr treeAnnotation = mCurrentTree.dynamicCast<TraceAnnotation>();

        mCurrentTree = treeAnnotation->next;
        mCurrentTrace = node->next;
        mCurrentTrace->accept(this);

        treeAnnotation->next = mCurrentTree;

        mCurrentTree = treeAnnotation;
        return;
    }

    qWarning() << "Warning, divergance discovered while merging a trace! (TraceAnnotation)";
    statistics()->accumulate("Concolic::ExecutionTree::DivergentMerges", 1);
    Log::info("  Trace merge diverged from the tree (TraceAnnotation).");
}

void TraceMerger::visit(TraceNode* node)
{
    qWarning() << "TraceNode reached, this indicates a missing case in the TraceMerger visitor!";
    exit(1);
}


// Checks whether the given node is an alert, page load or dom modification (with indicator words) and if so,
// decrements the appropriate statistics to account for "double-counting" them in the trace detectors.
void TraceMerger::fixDoubleCountedAnnotations(TraceNodePtr node)
{
    if(!node.dynamicCast<TraceAlert>().isNull()) {
        statistics()->accumulate("Concolic::ExecutionTree::Alerts", -1);
    } else if(!node.dynamicCast<TracePageLoad>().isNull()) {
        statistics()->accumulate("Concolic::ExecutionTree::PageLoads", -1);
    } else {
        QSharedPointer<TraceDomModification> domMod = node.dynamicCast<TraceDomModification>();
        if(!domMod.isNull() && domMod->words.size() > 0){ // Condition on words must match TraceDomModDetector::slDomModified().
            statistics()->accumulate("Concolic::ExecutionTree::InterestingDomModifications", -1);
        }

    }
}


}
