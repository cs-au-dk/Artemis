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

#ifndef KALUZASOLVER_H
#define KALUZASOLVER_H

#include "solver.h"

namespace artemis
{


/*
 *  Translates from our representation of path constraints to Kaluza's input language and runs Kaluza.
 */

class KaluzaSolver : Solver
{
public:
    KaluzaSolver();
    void solve(Symbolic::PathCondition pc); // TODO signature?
};


}


#endif // KALUZASOLVER_H
