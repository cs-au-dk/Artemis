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

#include "roundrobinselector.h"

namespace artemis
{


RoundRobinSelector::RoundRobinSelector(QList<AbstractSelectorPtr> selectors) : AbstractSelector()
{
    this->selectors = selectors;
    this->index = -1;
}

ExplorationDescriptor RoundRobinSelector::nextTarget(QList<ExplorationDescriptor> possibleTargets)
{
    this->index = (this->index + 1) % this->selectors.length();
    return (this->selectors.at(this->index))->nextTarget(possibleTargets);
}

void RoundRobinSelector::newTraceAdded(TraceNodePtr parent, int branch, TraceNodePtr next)
{
    for (int i = 0; i < this->selectors.size(); i++)
    {
      this->selectors.at(i)->newTraceAdded(parent, branch, next);
    }
}

void RoundRobinSelector::newUnsat(ExplorationDescriptor node)
{
    for (int i = 0; i < this->selectors.size(); i++)
    {
      this->selectors.at(i)->newUnsat(node);
    }
}

void RoundRobinSelector::newUnsolvable(ExplorationDescriptor node)
{
    for (int i = 0; i < this->selectors.size(); i++)
    {
      this->selectors.at(i)->newUnsolvable(node);
    }
}

void RoundRobinSelector::newMissed(ExplorationDescriptor node)
{
    for (int i = 0; i < this->selectors.size(); i++)
    {
      this->selectors.at(i)->newMissed(node);
    }
}


} // namespace artemis

