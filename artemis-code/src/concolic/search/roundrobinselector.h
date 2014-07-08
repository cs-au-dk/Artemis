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

#ifndef ROUNDROBINSELECTOR_H
#define ROUNDROBINSELECTOR_H

#include <QList>

#include "abstractselector.h"

namespace artemis
{


/**
    Combines a list of search strategies in a round robin way.
 */
class RoundRobinSelector : public AbstractSelector
{
public:
    /**
        Initializes this round robin selector.

        @param selectors the selectors that this selector combines.
        @pre. selectors is a nonempty list.
     */
    RoundRobinSelector(QList<AbstractSelectorPtr> selectors);

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
     */
    void newTraceAdded(TraceNodePtr node, int branch, TraceNodePtr suffix);

    /**
        Processes the notification that the given node (and its branch)
        gave rise to an unsatisfiable constraint.  Subclasses may override
        this method.

        @param node a node (and its branch).
     */
    void newUnsat(ExplorationDescriptor node);

    /**
        Processes the notification that the given node (and its branch)
        gave rise to a constraint that could not be solved.  Subclasses may
        override this method.

        @param node a node (and its branch).
     */
    void newUnsolvable(ExplorationDescriptor node);

    /**
        Processes the notification that the given node (and its branch) was
        missed, that is, although this node (and its branch) were expected
        to be part of the trace, they were not.  Subclasses may override this
        method.

        @param node a node (and its branch).
     */
    void newMissed(ExplorationDescriptor node);

private:
    /**
        List of selectors used in a round robin fashion.
     */
    QList<AbstractSelectorPtr> selectors;

    /**
        Index of the current selector.
     */
    int index;
};


} // namespace artemis
#endif // ROUNDROBINSELECTOR_H
