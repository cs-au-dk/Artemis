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

QSet<Symbolic::Expression *> ReachablePathsConstraintGenerator::generateConstraint(TraceNodePtr tree)
{
    // Call the visitor part to process the tree.
    // TODO

    // If the tree is all-terminating or all-aborting, then return a constant value.

    // Otherwise, we can just return the characterisation of the terminating paths whihc is already given in mSubtreeExpressions.

    // TODO
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

void ReachablePathsConstraintGenerator::visit(TraceConcreteBranch *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceSymbolicBranch *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceConcreteSummarisation *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceUnexplored *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceUnexploredUnsat *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceUnexploredUnsolvable *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceUnexploredMissed *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceUnexploredQueued *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceEndSuccess *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceEndFailure *node)
{

}

void ReachablePathsConstraintGenerator::visit(TraceEndUnknown *node)
{

}

// Annotation types are ignored; simply continue the visiting.
void ReachablePathsConstraintGenerator::visit(TraceAnnotation *node)
{
    node->next->accept(this);
}

// These are not part of the "real" tree; ignore.
void ReachablePathsConstraintGenerator::visit(TraceDivergence *node)
{
    node->next->accept(this);
}

} // namespace artemis
