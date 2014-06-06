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

#include <assert.h>
#include <QTime>

namespace artemis
{


RandomisedSearch::RandomisedSearch(TraceNodePtr tree, uint searchBudget) :
    RandomAccessSearch(tree, searchBudget)
{
    qsrand(QTime::currentTime().msec());
}

QPair<bool, RandomAccessSearch::ExplorationDescriptor> RandomisedSearch::nextTarget(QList<ExplorationDescriptor> possibleTargets)
{
    assert(possibleTargets.length() > 0);

    // Choose one of the possible targets at random and return it.
    int idx = qrand() % possibleTargets.length();

    return QPair<bool, RandomAccessSearch::ExplorationDescriptor>(true, possibleTargets.at(idx));
}



} //namespace artemis
