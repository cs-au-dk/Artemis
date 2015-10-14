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

#ifndef Z3SOLVER_H
#define Z3SOLVER_H

#include "solver.h"

namespace artemis
{

/*
 *  Generic symbolic constrint solver interface.
 */

class Z3Solver : public Solver
{
public:

    Z3Solver(ConcolicBenchmarkFeatures disabledFeatures);

    SolutionPtr solve(PathConditionPtr pc, FormRestrictions formRestrictions, DomSnapshotStoragePtr domSnapshots);

};

typedef QSharedPointer<Z3Solver> Z3SolverPtr;

}

#endif // Z3SOLVER_H
