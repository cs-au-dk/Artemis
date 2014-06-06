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

#include "dfstesting.h"

namespace artemis
{

DfsTesting::DfsTesting(TraceNodePtr tree, uint searchBudget, uint depthLimit) :
    RandomAccessSearch(tree, searchBudget),
    mDepthLimit(depthLimit)
{
}

QPair<bool, RandomAccessSearch::ExplorationDescriptor> DfsTesting::nextTarget(QList<RandomAccessSearch::ExplorationDescriptor> possibleTargets)
{
    // Choose the first node in the list which is within the depth limit.
    foreach (RandomAccessSearch::ExplorationDescriptor target, possibleTargets) {
        if (target.symbolicDepth <= mDepthLimit) {
            return QPair<bool, RandomAccessSearch::ExplorationDescriptor>(true, target);
        }
    }

    // If the list is empty or no nodes are above the depth limit, then stop the search.
    return QPair<bool, ExplorationDescriptor>(false, ExplorationDescriptor());
}

} //namespace artemis
