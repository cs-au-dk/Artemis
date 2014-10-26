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

#include "treemanager.h"

#include "tracevisitor.h"

namespace artemis
{

bool TreeManager::isUnexplored(ExplorationDescriptor target)
{
    return TraceVisitor::isImmediatelyUnexplored(targetRoot(target));
}

bool TreeManager::isQueuedOrNotAttempted(ExplorationDescriptor target)
{
    TraceNodePtr trace = targetRoot(target);
    return TraceVisitor::isImmediatelyQueued(trace) || TraceVisitor::isImmediatelyNotAttempted(trace);
}

void TreeManager::markNodeUnsat(ExplorationDescriptor target)
{
    setTargetBranch(target, TraceUnexploredUnsat::getInstance());
}

void TreeManager::markNodeUnsolvable(ExplorationDescriptor target)
{
    setTargetBranch(target, TraceUnexploredUnsolvable::getInstance());
}

void TreeManager::markNodeMissed(ExplorationDescriptor target)
{
    setTargetBranch(target, TraceUnexploredMissed::getInstance());
}

void TreeManager::markNodeQueued(ExplorationDescriptor target)
{
    setTargetBranch(target, TraceUnexploredQueued::getInstance());
}

void TreeManager::markExplorationIndex(ExplorationDescriptor target, uint index)
{
    assert(!target.branch.isNull());

    target.branch->markExploration(index, target.branchDirection);
}

TraceNodePtr TreeManager::targetRoot(ExplorationDescriptor target)
{
    assert(!target.branch.isNull());

    if (target.branchDirection) {
        return target.branch->getTrueBranch();
    } else {
        return target.branch->getFalseBranch();
    }
}

void TreeManager::setTargetBranch(ExplorationDescriptor target, TraceNodePtr newBranch)
{
    assert(!target.branch.isNull());
    assert(isQueuedOrNotAttempted(target)); // Sanity check for the calling code; not required here.

    if (target.branchDirection) {
        return target.branch->setTrueBranch(newBranch);
    } else {
        return target.branch->setFalseBranch(newBranch);
    }
}





} //namespace artemis
