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

#ifndef REACHABLEPATHSCONSTRAINTGENERATOR_H
#define REACHABLEPATHSCONSTRAINTGENERATOR_H

#include <QList>
#include <QPair>

#include "concolic/executiontree/tracenodes.h"
#include "concolic/executiontree/tracevisitor.h"
#include "reachablepathsconstraint.h"

namespace artemis
{

/*
 * Processes a (partial) execution tree to generate a constraint characterising all reachable paths.
 * That is, those paths which do not result in a "Failure" classification.
 *
 * This corresponds to the OverApprox constraints from the paper.
 *
 * Traces considered "good": Unexplored, End-Success, End-Unknown, Queued
 * Traces considered "bad": End-Failure
 * Ignored branches: UNSAT, CNS, Missed, unexplored children of concrete branches [all treated as "don't care"]
 * The returned constraint will exactly charaterise the "good" traces.
 *
 */
class ReachablePathsConstraintGenerator : public TraceVisitor
{
public:
    static ReachablePathsConstraintPtr generateConstraint(TraceNodePtr tree);

protected:
    ReachablePathsConstraintGenerator();
    ReachablePathsConstraintPtr mSubtreeExpression;

    // The visitor works from the bottom up, setting mSubtreeExpression to represent the set of all terminating traces.
    // If both sides of a branch are known to have the same value, then the branch can be dropped.
    // TODO: Currently this is only done for constants True and False, not for sub-expressions.
    // TODO: It would be better to have a check for constraint equality and merge all equal (even equivalent) branches.

    // Catch-all (error)
    virtual void visit(TraceNode* node);

    // Branches
    virtual void visit(TraceConcreteBranch* node);
    virtual void visit(TraceSymbolicBranch* node);
    virtual void visit(TraceConcreteSummarisation* node);

    // End markers we will use for the classification
    virtual void visit(TraceUnexplored* node);
    virtual void visit(TraceUnexploredUnsat* node);
    virtual void visit(TraceUnexploredUnsolvable* node);
    virtual void visit(TraceUnexploredMissed* node);
    virtual void visit(TraceUnexploredQueued* node);
    virtual void visit(TraceEndSuccess* node);
    virtual void visit(TraceEndFailure* node);
    virtual void visit(TraceEndUnknown* node);

    // Ignore
    virtual void visit(TraceAnnotation* node);
    virtual void visit(TraceDivergence* node);
};


} // namespace artemis
#endif // REACHABLEPATHSCONSTRAINTGENERATOR_H
