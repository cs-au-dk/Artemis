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
#include "concolic/executiontree/tracedisplay.h"

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
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
    }

    TraceMerger merger;

    merger.mStartingTrace = trace;
    merger.mStartingTree = executiontree;

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
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        return;
    }

    // case: trace end
    if (!mCurrentTrace->isEqualShallow(mCurrentTree)) {
        qWarning() << "Warning, divergance discovered while merging a trace! (TraceEnd)";
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DivergentMerges", 1);
        Log::info("  Trace merge diverged from the tree (TraceEnd).");
        reportFailedMerge();
    }
}

void TraceMerger::visit(TraceBranch* node)
{
    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        return;
    }

    // case: traceBranch
    if (node->isEqualShallow(mCurrentTree)) {

        TraceBranchPtr treeBranch = mCurrentTree.dynamicCast<TraceBranch>();

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
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::DivergentMerges", 1);
    Log::info("  Trace merge diverged from the tree (TraceBranch).");
    reportFailedMerge();
}

void TraceMerger::visit(TraceAnnotation* node)
{
    // case: unexplored branch in the tree
    if (TraceVisitor::isImmediatelyUnexplored(mCurrentTree)) {

        // Insert this trace directly into the tree and return
        mCurrentTree = mCurrentTrace;
        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        return;
    }

    if (node->isEqualShallow(mCurrentTree)) {
        TraceAnnotationPtr treeAnnotation = mCurrentTree.dynamicCast<TraceAnnotation>();

        mCurrentTree = treeAnnotation->next;
        mCurrentTrace = node->next;
        mCurrentTrace->accept(this);

        treeAnnotation->next = mCurrentTree;

        mCurrentTree = treeAnnotation;
        return;
    }

    qWarning() << "Warning, divergance discovered while merging a trace! (TraceAnnotation)";
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::DivergentMerges", 1);
    Log::info("  Trace merge diverged from the tree (TraceAnnotation).");
    reportFailedMerge();
}

void TraceMerger::visit(TraceNode* node)
{
    qWarning() << "TraceNode reached, this indicates a missing case in the TraceMerger visitor!";
    exit(1);
}


// When we find a divergent merge, this function writes the entire original tree and trace out to a file for manual analysis.
void TraceMerger::reportFailedMerge()
{
    if(mReportFailedMerge){
        QString date = QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss");
        QString pathToTreeFile = QString("divergence-%1-tree.gv").arg(date);
        QString pathToTraceFile = QString("divergence-%1-trace.gv").arg(date);

        TraceDisplay display;

        display.writeGraphFile(mStartingTree, pathToTreeFile, false);
        display.writeGraphFile(mStartingTrace, pathToTraceFile, false);
    }
}



}
