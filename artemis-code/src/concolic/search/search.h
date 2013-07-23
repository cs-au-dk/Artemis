/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "concolic/executiontree/tracenodes.h"

#ifndef SEARCH_H
#define SEARCH_H




namespace artemis
{



/*
 *  Abstract interface for searching for the next node to explore in the path tree.
 */

// TODO: decide which methods from DepthFirstSearch should become part of this interface!

class TreeSearch : public TraceVisitor
{
public:
    virtual TraceUnexplored* chooseNextTarget() = 0;
    // N.B. We need to use a standard pointer here as that is all we get from the vsitor which does the searching.
    // The pointer returned by this is owned by the tree (and possibly others) and is only valid while the node is still in the tree (i.e. until the next run).
};




}

#endif // SEARCH_H
