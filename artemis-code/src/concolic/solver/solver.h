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

#ifndef SOLVER_H
#define SOLVER_H

#include <QSharedPointer>

#include "JavaScriptCore/symbolic/pathcondition.h"

#include "solution.h"

namespace artemis
{

/*
 *  Generic symbolic constrint solver interface.
 */

class Solver
{
public:
    static SolutionPtr solve(QSharedPointer<Symbolic::PathCondition> pc);

private:
    Solver();
};




}

#endif // SOLVER_H
