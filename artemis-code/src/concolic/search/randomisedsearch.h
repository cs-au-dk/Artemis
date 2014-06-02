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

#ifndef RANDOMISEDSEARCH_H
#define RANDOMISEDSEARCH_H

#include "randomaccesssearch.h"

namespace artemis
{

/**
 *  This is an example implementation of RandomAccessSearch which chooses nodes to explore at random.
 */

class RandomisedSearch : public RandomAccessSearch
{
public:
    RandomisedSearch(TraceNodePtr tree, unsigned int searchAttempts);

protected:
    // Chooses between the possible exploration targets.
    QPair<bool, ExplorationDescriptor> nextTarget(QSet<ExplorationDescriptor> possibleTargets);

private:
    unsigned int mSearchAttempts;
};


} //namespace artemis
#endif // RANDOMISEDSEARCH_H
