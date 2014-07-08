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

#ifndef AVOIDUNSATSELECTOR_H
#define AVOIDUNSATSELECTOR_H

#include <QHash>
#include <QPair>

#include "concolic/executiontree/tracevisitor.h"
#include "abstractselector.h"

namespace artemis
{


/**
    This class implements a selector that tries to avoid constraints that are
    unsatisfiable.
 */
class AvoidUnsatSelector : public AbstractSelector, public TraceVisitor
{
public:
    /**
        Initializes this selector.
     */
    AvoidUnsatSelector();

    /**
        Selects a node (and one of its branches) from the given list.
        In general, the list will represent the unexplored nodes of the tree.

        @param possibleTargets a list of nodes (and their branches).
        @pre. possibleTargets is a nonempty list.
        @return a node (and one of its branches) from the list.
     */
    ExplorationDescriptor nextTarget(QList<ExplorationDescriptor> possibleTargets);

    /**
        Processes the notification that a new trace has been added to the
        tree.  Note that this method may not always be called between calls
        to the nextTarget method.  This method is also called on the initial
        trace with a null parent.

        @param parent the last node of the new trace that was already part
        of the tree (it can be concrete branch, symbolic branch or concrete
        summary).
        @param branch the branch of the parent node in the new trace.
        @param next the next node in the new trace.
        @param fullTrace the entire recorded trace, including the prefix which is not part of the tree.
     */
    void newTraceAdded(TraceNodePtr node, int branch, TraceNodePtr suffix, TraceNodePtr fullTrace);

    /**
        Processes the notification that the given node (and its branch)
        gave rise to an unsatisfiable constraint.

        @param node a node (and its branch).
     */
    void newUnsat(ExplorationDescriptor node);

private:
     /**
        Probability of choosing the best unexplored node.  With the remaining
        probability an unexplored node is chosen randomly.
     */
    static const double P = 0.9;

    /**
        Given the id of a branching instruction (represented by a pair of 
        uints) and a branch (represented by a bool), the number of times
        the branch led a satisfiable and unsatisfiable constraint, respectively.
     */
    QHash<QPair<QPair<uint, uint>, bool>, QPair<uint, uint> > counts;

    /**
        Returns the id of the given node pointer and branch.

        @param node a node pointer.
        @param branch a branch of the node.
        @return the id of the given node and branch.
     */
    static QPair<QPair<uint, uint>, bool> getId(TraceBranchPtr node, bool branch);


    /**
        Returns the id of the given node and branch.

        @param node a node.
        @param branch a branch of the node.
        @return the id of the given node and branch.
     */
    static QPair<QPair<uint, uint>, bool> getId(TraceBranch* node, bool branch);

    /**
        Returns the value of the given node and branch.

        @param node a node (and its branch).
        @return the value of the given node and branch.
     */
    double getValue(ExplorationDescriptor target);

    /**
        Updates the satisfiability/unsatisfiability of the constraint related
        to the given node.

        @param node a node of a trace that has been added to the tree.
     */
    void visit(TraceNode* node);

    /**
        Updates the satisfiability/unsatisfiability of the constraint related
        to the given node.

        @param node a node of a trace that has been added to the tree.
     */
    void visit(TraceConcreteBranch* node);

    /**
        Updates the satisfiability/unsatisfiability of the constraint related
        to the given node.

        @param node a node of a trace that has been added to the tree.
     */
    void visit(TraceSymbolicBranch* node);

    /**
        Updates the satisfiability/unsatisfiability of the constraint related
        to the given node.

        @param node a node of a trace that has been added to the tree.
     */
    void visit(TraceConcreteSummarisation *node);

    /**
        Updates the satisfiability/unsatisfiability of the constraint related
        to the given node.

        @param node a node of a trace that has been added to the tree.
     */
    void visit(TraceUnexplored* node);

    /**
        Updates the satisfiability/unsatisfiability of the constraint related
        to the given node.

        @param node a node of a trace that has been added to the tree.
     */
    void visit(TraceAnnotation* node);

    /**
        Updates the satisfiability/unsatisfiability of the constraint related
        to the given node.

        @param node a node of a trace that has been added to the tree.
     */
    void visit(TraceEnd* node);
};


} // namespace artemis
#endif // AVOIDUNSATSELECTOR_H
