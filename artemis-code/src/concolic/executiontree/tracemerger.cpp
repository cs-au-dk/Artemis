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
#include <assert.h>
#include <QDebug>

#include "util/loggingutil.h"
#include "concolic/executiontree/tracedisplay.h"

#include "tracemerger.h"

namespace artemis
{

TraceNodePtr TraceMerger::merge(TraceNodePtr trace, TraceNodePtr executiontree, TraceNodePtr* executionTreeRootPtr)
{
    if (trace.isNull()) {
        return executiontree;
    }

    if (executiontree.isNull()) {
        return trace; // replace the entire execution tree with the trace
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
    }

    mStartingTrace = trace;
    mStartingTreeRootPtr = executionTreeRootPtr;

    mCurrentTrace = trace;
    mCurrentTree = executiontree;

    mPreviousParent = TraceNodePtr();
    mPreviousDirection = 0;

    mImmediateParent = TraceNodePtr();
    mImmediateParentDirection = 0;

    mMergingDivergence = false;

    trace->accept(this);

    return mCurrentTree;
}

void TraceMerger::visit(TraceUnexplored* node)
{
    // Ignore, we can't add any information to the execution tree
    return;
}

void TraceMerger::visit(TraceEnd* node)
{
    TraceDivergencePtr skipped = skipDivergenceNodesInTree();

    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        unSkipDivergenceNodesInTree(skipped);
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        reportMerge(mCurrentTrace);
        return;
    }

    // case: trace end
    if (mCurrentTrace->isEqualShallow(mCurrentTree)) {
        // Merge the exploration indices.
        TraceEndPtr treeEnd =  mCurrentTree.dynamicCast<TraceEnd>();
        treeEnd->traceIndices.unite(node->traceIndices);
        unSkipDivergenceNodesInTree(skipped);

    } else {
        handleDivergence();
    }
}

void TraceMerger::visit(TraceBranch* node)
{
    TraceDivergencePtr skipped = skipDivergenceNodesInTree();

    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        unSkipDivergenceNodesInTree(skipped);
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        reportMerge(mCurrentTrace);
        return;
    }

    // case: traceBranch
    if (node->isEqualShallow(mCurrentTree)) {

        TraceBranchPtr treeBranch = mCurrentTree.dynamicCast<TraceBranch>();

        // Merge the traces for each branch

        mCurrentTree = treeBranch->getTrueBranch();
        mCurrentTrace = node->getTrueBranch();
        mPreviousParent = treeBranch;
        mPreviousDirection = 1;
        mImmediateParent = treeBranch;
        mImmediateParentDirection = 1;
        mCurrentTrace->accept(this);

        treeBranch->setTrueBranch(mCurrentTree);

        mCurrentTree = treeBranch->getFalseBranch();
        mCurrentTrace = node->getFalseBranch();
        mPreviousParent = treeBranch;
        mPreviousDirection = 0;
        mImmediateParent = treeBranch;
        mImmediateParentDirection = 0;
        mCurrentTrace->accept(this);

        treeBranch->setFalseBranch(mCurrentTree);

        mCurrentTree = treeBranch;
        unSkipDivergenceNodesInTree(skipped);
        return;
    }

    handleDivergence();
}

void TraceMerger::visit(TraceAnnotation* node)
{
    TraceDivergencePtr skipped = skipDivergenceNodesInTree();

    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        unSkipDivergenceNodesInTree(skipped);
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        reportMerge(mCurrentTrace);
        return;
    }

    if (node->isEqualShallow(mCurrentTree)) {
        TraceAnnotationPtr treeAnnotation = mCurrentTree.dynamicCast<TraceAnnotation>();

        mCurrentTree = treeAnnotation->next;
        mCurrentTrace = node->next;
        mImmediateParent = treeAnnotation;
        mImmediateParentDirection = 0;
        mCurrentTrace->accept(this);

        treeAnnotation->next = mCurrentTree;

        mCurrentTree = treeAnnotation;
        unSkipDivergenceNodesInTree(skipped);
        return;
    }

    handleDivergence();
}


void TraceMerger::visit(TraceConcreteSummarisation *node)
{
    TraceDivergencePtr skipped = skipDivergenceNodesInTree();

    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        unSkipDivergenceNodesInTree(skipped);
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        reportMerge(mCurrentTrace);
        return;
    }

    if (node->isEqualShallow(mCurrentTree)) {
        TraceConcreteSummarisationPtr treeSummary = mCurrentTree.dynamicCast<TraceConcreteSummarisation>();

        // Check that the event sequences from these two summaries can be merged.

        // The trace summary is assumed to have a single execution path.
        // To merge it with the tree, we check each of the execution paths in the tree node in turn.
        // For each tree node execution sequence:
        //     If the sequences match perfectly, then this is a match and we are done. Continue merging the children.
        //     If the sequences have matching prefixes until a BRANCH_TRUE and BRANCH_FALSE, then this is is a
        //       fully explored concrete branch which does not match this execution so move on to the next.
        //     If the sequences first diverge without a BRANCH_TRUE and BRANCH_FALSE then this is a trace divergence.
        // If the end of the list of executions is reached and the trace still has not been matched or marked as a
        //   divergence then it must be a new branch point and is added to the list.

        // Check the trace has a unique execution path.
        if(node->executions.length() != 1) {
            Log::fatal("Attempting to merge a trace with multiple concrete execution paths within a summary node.");
            exit(1);
        }
        QPair<QList<TraceConcreteSummarisation::EventType>, TraceNodePtr> traceExec = node->executions[0];

        // Attempt to match with each tree execution path in turn.
        int idx = 0;
        foreach(TraceConcreteSummarisation::SingleExecution treeExec, treeSummary->executions) {

            // If the executions match exactly then merge the successor nodes and end.
            if(treeExec.first == traceExec.first) {
                mCurrentTree = treeExec.second;
                mCurrentTrace = traceExec.second;
                mPreviousParent = treeSummary;
                mPreviousDirection = idx;
                mImmediateParent = treeSummary;
                mImmediateParentDirection = idx;
                mCurrentTrace->accept(this);

                treeExec.second = mCurrentTree;

                mCurrentTree = treeSummary;
                unSkipDivergenceNodesInTree(skipped);
                return;
            }

            // Otherwise, we need to check the first difference between them.
            bool goodMatch = false;
            int len = min(treeExec.first.length(), traceExec.first.length());
            for(int i = 0; i < len; i++) {
                if(treeExec.first[i] != traceExec.first[i]){
                    qDebug() << "found mismatch!" << treeExec.first[i] << traceExec.first[i];

                    if(treeExec.first[i] == TraceConcreteSummarisation::FUNCTION_CALL ||
                            traceExec.first[i] == TraceConcreteSummarisation::FUNCTION_CALL) {
                        // The traces diverged but not at BRANCH_TRUE and BRANCH_FALSE.
                        mAlreadyMismatched.insert(treeSummary);
                        handleDivergence();
                        return;

                    } else {
                        // The traces have differed at BRANCH_TRUE vs BRANCH_FALSE.
                        // So we should continue the outer loop to check if any other traces will match it.
                        goodMatch = true;
                        break;
                    }
                }
            }

            if(!goodMatch) {
                // If we reach here then one must be shorter than the other (but matches a prefix).
                // This counts as a divergence, as one trace will continue with the summary while the other goes on to
                // an "interesting" node.
                mAlreadyMismatched.insert(treeSummary);
                handleDivergence();
                return;
            }

            idx++;
        }

        // If we have checked each execution without finding a match or a divergence, then this is a valid new path.
        // Insert the new path into the tree and return.
        treeSummary->executions.append(traceExec);
        // mCurrentTree is not changed.
        unSkipDivergenceNodesInTree(skipped);
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        mPreviousParent = treeSummary;
        mPreviousDirection = treeSummary->executions.length()-1;
        reportMerge(traceExec.second);
        return;
    }

    // Corresponding tree node was not a concrete summary.
    handleDivergence();
}


void TraceMerger::visit(TraceNode* node)
{
    qWarning() << "TraceNode reached, this indicates a missing case in the TraceMerger visitor!";
    exit(1);
}

void TraceMerger::visit(TraceDivergence* node)
{
    qWarning() << "TraceDivergence reached, which is not expected in the recorded trace in the TraceMerger visitor!";
    exit(1);
}


// When we find a divergent merge, this function inserts the divergence node into the tree to record it.
void TraceMerger::handleDivergence()
{
    qWarning() << "Warning, divergance discovered while merging a trace!";
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::DivergentMerges", 1);
    Log::info("  Trace merge diverged from the tree.");

    // Use mImmediateParent[Direction] and mCurrentTree to insert a new TraceDivergence into the tree.

    if (mImmediateParent.isNull()) {
        // If there is a divergence at the root, we need to overwrite the root pointer (a hack) and replace it with a new divergence node.
        handleDivergenceAtRoot();
        return;
    }

    // Check if mImmediateParent is already a divergence node, otherwise we will create a new one.
    TraceDivergencePtr parentDivergence = mImmediateParent.dynamicCast<TraceDivergence>();
    if (parentDivergence.isNull()) {
        TraceDivergencePtr divergence = TraceDivergencePtr(new TraceDivergence());
        divergence->next = mCurrentTree;
        addDivergentTraceToNode(divergence, mCurrentTrace);

        mImmediateParent->setChild(mImmediateParentDirection, divergence); // Replaces the pointer to mCurrentTree with divercence in the immediate parent node.
        mCurrentTree = divergence;

    } else {
        addDivergentTraceToNode(parentDivergence, mCurrentTrace);
        mCurrentTree = parentDivergence;
    }
}

void TraceMerger::addDivergentTraceToNode(TraceDivergencePtr node, TraceNodePtr trace)
{
    // Try to merge this trace with one of the existing divergent traces, if possible.
    // If there is an existing divergence with a matching head node, then just recursively merge the traces as normal.
    // Otherwise just append the new trace to the list of divergences.

    bool matched = false;
    foreach (TraceNodePtr head, node->divergedTraces) {
        if (!mAlreadyMismatched.contains(head) && trace->isEqualShallow(head)) {
            mMergingDivergence = true;

            mCurrentTree = head;
            mCurrentTrace = trace;
            // mPreviousParent, mPreviousDirection as before.
            mImmediateParent = node;
            mImmediateParentDirection = node->divergedTraces.indexOf(head);

            mCurrentTrace->accept(this);

            mMergingDivergence = false;

            matched = true;
            mAlreadyMismatched.clear();
            break;
        }
    }
    if (!matched) {
        node->divergedTraces.append(trace);
    }
}

void TraceMerger::handleDivergenceAtRoot()
{
    Log::info("  Trace merge diverged immediately. Modifying the root.");

    // HACK: Use mStartingTreeRootPtr to replace the tree pointer in the calling code with one to a new divergence branch.

    TraceDivergencePtr divergence = TraceDivergencePtr(new TraceDivergence());
    divergence->next = mCurrentTree;
    addDivergentTraceToNode(divergence, mCurrentTrace); // Same as mStartingTrace here.

    *mStartingTreeRootPtr = divergence;
    mCurrentTree = divergence;
}

TraceDivergencePtr TraceMerger::skipDivergenceNodesInTree()
{
    TraceDivergencePtr head = mCurrentTree.dynamicCast<TraceDivergence>();
    if (head.isNull()) {
        return TraceDivergencePtr();
    }

    // Sanity check for more than one divergence in a row.
    TraceDivergencePtr nextnode = head->next.dynamicCast<TraceDivergence>();
    if (!nextnode.isNull()) {
        Log::fatal("Found two divergence branches in a row, which is an error in the TraceMerger.");
        exit(1);
    }

    // If everythingis ok, fast-forward one node.
    mImmediateParent = head;
    mImmediateParentDirection = 0;
    mCurrentTree = head->next;

    return head;
}

void TraceMerger::unSkipDivergenceNodesInTree(TraceDivergencePtr node)
{
    if (!node.isNull()) {
        mCurrentTree = node;
    }
}

// When we merge a trace, trigger the signals.
void TraceMerger::reportMerge(TraceNodePtr newPart)
{
    assert(!mPreviousParent.isNull());
    if (!mMergingDivergence) {
        emit sigTraceJoined(mPreviousParent, mPreviousDirection, newPart, mStartingTrace);
    }
}




}
