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

#include "randomisedsearch.h"

namespace artemis
{


RandomisedSearch::RandomisedSearch(TraceNodePtr tree, unsigned int searchAttempts) :
    RandomAccessSearch(tree),
    mSearchAttempts(searchAttempts)
{
}

QPair<bool, RandomAccessSearch::ExplorationDescriptor> RandomisedSearch::nextTarget(QList<ExplorationDescriptor> possibleTargets)
{
    // If we have run out of attempts, then return false.
    if (mSearchAttempts < 1 || possibleTargets.empty()) {
        return QPair<bool, ExplorationDescriptor>(false, ExplorationDescriptor());
    }

    // Otherwise choose one of the possible targets at random and return it.
    int idx = qrand() % possibleTargets.length();

    mSearchAttempts--;

    return QPair<bool, RandomAccessSearch::ExplorationDescriptor>(true, possibleTargets.at(idx));
}



} //namespace artemis
