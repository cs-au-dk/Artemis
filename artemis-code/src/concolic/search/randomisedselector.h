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

#ifndef RANDOMISEDSELECTOR_H
#define RANDOMISEDSELECTOR_H

#include "randomaccesssearch.h"
#include "abstractselector.h"

namespace artemis
{


/**
   This is an example implementation of a selector which chooses nodes to 
   explore at random.
 */
class RandomisedSelector : public AbstractSelector
{
public:
    /**
        Initializes this selector.
     */
    RandomisedSelector();

    /**
        Selects a node (and one of its branches) from the given list.
        In general, the list will represent the unexplored nodes of the tree.

        @param possibleTargets a list of nodes (and their branches).
        @pre. possibleTargets is a nonempty list.
        @return a node (and one of its branches) from the list.
     */
    ExplorationDescriptor nextTarget(QList<ExplorationDescriptor> possibleTargets);
};


} //namespace artemis
#endif // RANDOMISEDSELECTOR_H
