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

#include <stdlib.h>
#include <QDebug>

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

        // Merge the traces for each branch

        TraceBranchPtr treeBranch = mCurrentTree.dynamicCast<TraceBranch>();

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

        TraceAnnotationPtr treeAnnotation = mCurrentTree.dynamicCast<TraceAnnotation>();

        mCurrentTree = treeAnnotation->next;
        mCurrentTrace = node->next;
        mCurrentTrace->accept(this);

        treeAnnotation->next = mCurrentTree;

        mCurrentTree = treeAnnotation;
        return;
    }

    qWarning() << "Warning, divergance discovered while merging a trace! (TraceAnnotation)";
}

void TraceMerger::visit(TraceNode* node)
{
    qWarning() << "TraceNode reached, this indicates a missing case in the TraceMerger visitor!";
    exit(1);
}


}
