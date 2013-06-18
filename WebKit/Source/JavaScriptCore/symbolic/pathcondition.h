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

#ifndef PATHCONDITION_H
#define PATHCONDITION_H

#include <inttypes.h>
#include <vector>
#include <utility>

#include "JavaScriptCore/symbolic/expression/expression.h"

#ifdef ARTEMIS

namespace Symbolic
{

// TODO we need to figure out how to do memory management of this data structure

class PathCondition
{
public:
    PathCondition();

    void append(Symbolic::Expression* condition, bool followed);
    std::pair<Symbolic::Expression*, bool> get(unsigned int index);
    int size() const;

private:
    std::vector<std::pair<Symbolic::Expression*, bool> > m_pc;
};

}

#endif
#endif // PATHCONDITION_H
