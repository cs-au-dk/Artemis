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

#include "concolic/executiontree/nodes/tracesymbolicbranch.h"

#ifndef EXPLORATIONDESCRIPTOR_H
#define EXPLORATIONDESCRIPTOR_H

namespace artemis
{

/**
 *  Used by RandomAccessSearch and the selectors system.
 */
struct ExplorationDescriptor {
    // The parent branch of the unexplored node.
    TraceSymbolicBranchPtr branch;
    // The child of the branch which is unexplored.
    bool branchDirection;

    // Information which may be useful to some of the selectors:
    unsigned int symbolicDepth;

    // Hash and equality operators so it can be put into sets, etc.
    friend inline bool operator==(const ExplorationDescriptor& a, const ExplorationDescriptor& b)
    {
        return a.branch == b.branch && a.branchDirection == b.branchDirection ;
    }

    friend inline uint qHash(const ExplorationDescriptor& key)
    {
        return ::qHash(key.branch) ^ ::qHash((int)key.branchDirection);
    }
};



} // namespace artemis
#endif // EXPLORATIONDESCRIPTOR_H
