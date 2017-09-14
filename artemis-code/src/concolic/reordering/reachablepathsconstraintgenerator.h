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

#ifndef REACHABLEPATHSCONSTRAINTGENERATOR_H
#define REACHABLEPATHSCONSTRAINTGENERATOR_H

namespace artemis
{

/*
 * Processes a (partial) execution tree to generate a constraint characterising all reachable paths.
 * That is, those paths which do not result in a "Failure" classification.
 *
 * This corresponds to the OverApprox constraints from the paper.
 *
 * Traces considered "good": Unexplored, End-Success, End-Unknown
 * Traces considered "bad": End-Failure
 * Ignored branches: UNSAT, CNS [treated as "don't care"]
 * The returned constraint will exactly charaterise the "good" traces.
 *
 */
class ReachablePathsConstraintGenerator : public TraceVisitor
{
public:
    QSet<Symbolic::Expression*> generateConstraint(TraceNodePtr tree);

protected:
    ReachablePathsConstraintGenerator();
    bool mSubtreeAllOk;
    bool mSubtreeAllAbort;
    QSet<Symbolic::Expression*> mSubtreeExpressions;

    // The visitor works from the bottom up.
    // If the curent subtree only contains known good or known bad nodes, then mSubtreeAllOK or mSubtreeAllAbort are
    // set, and mSubTreeExpressions is empty.
    // If the current subtree contains a mix of terminating and aborting branches, the the flags are both unset,
    // and mSubtreeExpressions contains the set of symbolic expressions whihch correspond to terminating traces.

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
