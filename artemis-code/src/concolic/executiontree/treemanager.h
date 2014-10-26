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

#include "concolic/search/explorationdescriptor.h"
#include "concolic/executiontree/tracenodes.h"

#ifndef TREEMANAGER_H
#define TREEMANAGER_H

namespace artemis
{


class TreeManager
{
public:

    // Returns true if the node is not attempted, UNSAT, unsolvable, or missed.
    static bool isUnexplored(ExplorationDescriptor target);
    // Returns true if the node has not yet been attempted (UNSAT etc. return false).
    static bool isQueuedOrNotAttempted(ExplorationDescriptor target);

    static void markNodeUnsat(ExplorationDescriptor target);
    static void markNodeUnsolvable(ExplorationDescriptor target);
    static void markNodeMissed(ExplorationDescriptor target);
    static void markNodeQueued(ExplorationDescriptor target);

    static void markExplorationIndex(ExplorationDescriptor target, uint index);

protected:
    static TraceNodePtr targetRoot(ExplorationDescriptor target);
    static void setTargetBranch(ExplorationDescriptor target, TraceNodePtr newBranch);
};


} //namespace artemis
#endif // TREEMANAGER_H
