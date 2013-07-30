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
#include "concolic/pathcondition.h"

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
    virtual bool chooseNextTarget() = 0;     // Returns true iff a target was found.
    virtual PathCondition getTargetPC() = 0; // Returns the target's PC after a call to chooseNextTarget() returns true.
};




}

#endif // SEARCH_H
