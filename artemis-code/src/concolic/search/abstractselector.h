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

#ifndef ABSTRACTSELECTOR_H
#define ABSTRACTSELECTOR_H

#include "explorationdescriptor.h"

#include "concolic/executiontree/nodes/trace.h"

namespace artemis
{


/**
    This class provides a base implementation for a selector.  A selector 
    chooses which branch of which node to explore next.  Furthermore, a 
    selector is notified whenever
    a new trace has been added to the tree,
    an unsatisfied constraint was encountered,
    a constraint could not be solved, and
    a branch of a node was missed.

    A concrete selector inherits from this class and implements the 
    nextTarget method  to choose which branch of which node to explore next.  
    Furthermore, a concrete selector may implement any of the notification 
    methods.  The data collected from these notifications can be  used in 
    the nextTarget method.
 */
class AbstractSelector
{
public:

    /**
        Selects a node (and one of its branches) from the given list.  
        Subclasses should override this method.  In general, the list will
        represent the unexplored nodes of the tree.

        @param possibleTargets a list of nodes (and their branches).
        @pre. possibleTargets is a nonempty list.
        @return a node (and one of its branches) from the list.
     */
    virtual ExplorationDescriptor nextTarget(QList<ExplorationDescriptor> possibleTargets) = 0;

    /**
        Processes the notification that a new trace has been added to the 
        tree.  Subclasses may override this method.  Note that this method
        may not always be called between calls to the nextTarget method.
        This method is also called on the initial trace with a null parent.

        @param parent the last node of the new trace that was already part 
        of the tree (it can be concrete branch, symbolic branch or concrete
        summary).
        @param branch the branch of the parent node in the new trace.
        @param next the next node in the new trace.
     */
    virtual void newTraceAdded(TraceNodePtr parent, int branch, TraceNodePtr next) {}

    /**
        Processes the notification that the given node (and its branch) 
        gave rise to an unsatisfiable constraint.  Subclasses may override
        this method.

        @param node a node (and its branch).
     */
    virtual void newUnsat(ExplorationDescriptor node) {}

    /**
        Processes the notification that the given node (and its branch) 
        gave rise to a constraint that could not be solved.  Subclasses may
        override this method.

        @param node a node (and its branch).
     */
    virtual void newUnsolvable(ExplorationDescriptor node) {}

    /**
        Processes the notification that the given node (and its branch) was 
        missed, that is, although this node (and its branch) were expected
        to be part of the trace, they were not.  Subclasses may override this
        method.

        @param node a node (and its branch).
     */
    virtual void newMissed(ExplorationDescriptor node) {}

    /**
     *   Virtual destructor.
     */
    virtual ~AbstractSelector() {}

};

typedef QSharedPointer<AbstractSelector> AbstractSelectorPtr;


} // namespace artemis
#endif // ABSTRACTSELECTOR_H
