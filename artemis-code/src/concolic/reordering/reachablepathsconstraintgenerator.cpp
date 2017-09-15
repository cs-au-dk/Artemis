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

#include "reachablepathsconstraintgenerator.h"

namespace artemis
{

ReachablePathsConstraintPtr ReachablePathsConstraintGenerator::generateConstraint(TraceNodePtr tree)
{
    // Call the visitor part to process the tree.
    ReachablePathsConstraintGenerator generator;
    tree->accept(&generator);
    return generator.mSubtreeExpression;
}

ReachablePathsConstraintGenerator::ReachablePathsConstraintGenerator()
{
}

// We cover all ther cases below so this should never be called.
void ReachablePathsConstraintGenerator::visit(TraceNode *node)
{
    Log::fatal("Getting the reachable paths constraint for a trace node of an unknown type.");
    exit(1);
}

void ReachablePathsConstraintGenerator::visit(TraceConcreteBranch* node)
{
    // If one branch is unexplored (or queued), then ignore.
    // Also ignore UNSAT, CNS, and Missed branches [although these should never appear under a concrete branch!].
    if (isImmediatelyUnexplored(node->getFalseBranch())) {
        node->getTrueBranch()->accept(this);
        return;
    }
    if (isImmediatelyUnexplored(node->getTrueBranch())) {
        node->getFalseBranch()->accept(this);
        return;
    }

    // If both branches are explored, then what...?
    // TODO
}

void ReachablePathsConstraintGenerator::visit(TraceSymbolicBranch* node)
{
    // If one branch is of an ignored type (UNSAT, CNS, missed), then we can return the other branch directly.
    if (isImmediatelyUnsat(node->getFalseBranch())
            || isImmediatelyMissed(node->getFalseBranch())
            || isImmediatelyUnsolvable(node->getFalseBranch())) {
        node->getTrueBranch()->accept(this);
        return;
    }
    if (isImmediatelyUnsat(node->getTrueBranch())
            || isImmediatelyMissed(node->getTrueBranch())
            || isImmediatelyUnsolvable(node->getTrueBranch())) {
        node->getFalseBranch()->accept(this);
        return;
    }

    // Run the visitor on each branch.
    node->getFalseBranch()->accept(this);
    ReachablePathsConstraintPtr falseConstraint = mSubtreeExpression;

    node->getTrueBranch()->accept(this);
    ReachablePathsConstraintPtr trueConstraint = mSubtreeExpression;

    // If both subtrees are true or false, we can return directly.
    if (falseConstraint->isAlwaysTerminating() && trueConstraint->isAlwaysTerminating()) {
        mSubtreeExpression = ReachablePathsOk.getInstance();
    } else if (falseConstraint->isAlwaysAborting() && trueConstraint->isAlwaysAborting()) {
        mSubtreeExpression = ReachablePathsAbort.getInstance();
    } else {
        // Otherwise, generate an ITE constraint.
        QSharedPointer<ReachablePathsITE> newExpr = QSharedPointer<ReachablePathsITE>(new ReachablePathsITE());
        newExpr->condition = node->getSymbolicCondition();
        newExpr->thenConstraint = trueConstraint;
        newExpr->elseConstraint = falseConstraint;
        mSubtreeExpression = newExpr;
    }
}

void ReachablePathsConstraintGenerator::visit(TraceConcreteSummarisation* node)
{
    // If there is just a single child (a very common case), then we can just return its value directly.
    if (node->executions.length() == 1) {
        node->executions[0].second->accept(this);
        return;
    }


    // If there are multiple children, then what...?
    // TODO
}

void ReachablePathsConstraintGenerator::visit(TraceUnexplored* node)
{
    mSubtreeExpression = ReachablePathsOk.getInstance();
}

void ReachablePathsConstraintGenerator::visit(TraceUnexploredUnsat* node)
{
    // Should be handled in the branch nodes.
    Log::fatal("ReachablePathsConstraintGenerator should not visit TraceUnexploredUnsat directly.");
    exit(1);
}

void ReachablePathsConstraintGenerator::visit(TraceUnexploredUnsolvable* node)
{
    // Should be handled in the branch nodes.
    Log::fatal("ReachablePathsConstraintGenerator should not visit TraceUnexploredUnsolvable directly.");
    exit(1);
}

void ReachablePathsConstraintGenerator::visit(TraceUnexploredMissed* node)
{
    // Should be handled in the branch nodes.
    Log::fatal("ReachablePathsConstraintGenerator should not visit TraceUnexploredMissed directly.");
    exit(1);
}

void ReachablePathsConstraintGenerator::visit(TraceUnexploredQueued* node)
{
    // Should be handled in the branch nodes.
    Log::fatal("ReachablePathsConstraintGenerator should not visit TraceUnexploredQueued directly.");
    exit(1);
}

void ReachablePathsConstraintGenerator::visit(TraceEndSuccess* node)
{
    mSubtreeExpression = ReachablePathsOk.getInstance();
}

void ReachablePathsConstraintGenerator::visit(TraceEndFailure* node)
{
    mSubtreeExpression = ReachablePathsAbort.getInstance();
}

void ReachablePathsConstraintGenerator::visit(TraceEndUnknown* node)
{
    mSubtreeExpression = ReachablePathsOk.getInstance();
}

// Annotation types are ignored; simply continue the visiting.
void ReachablePathsConstraintGenerator::visit(TraceAnnotation* node)
{
    node->next->accept(this);
}

// These are not part of the "real" tree; ignore.
void ReachablePathsConstraintGenerator::visit(TraceDivergence* node)
{
    node->next->accept(this);
}

} // namespace artemis
