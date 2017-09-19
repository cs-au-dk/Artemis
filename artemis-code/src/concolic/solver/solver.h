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

#ifndef SOLVER_H
#define SOLVER_H

#include <QSharedPointer>

#include "concolic/pathcondition.h"
#include "runtime/input/forms/formfieldrestrictedvalues.h"
#include "model/domsnapshotstorage.h"
#include "concolic/benchmarking.h"
#include "runtime/options.h"
#include "concolic/reordering/reachablepathsconstraint.h"
#include "concolic/reordering/concolicvariablerenamer.h"

#include "solution.h"

namespace artemis
{

/*
 *  Generic symbolic constrint solver interface.
 */

class Solver
{
public:

    Solver(ConcolicBenchmarkFeatures disabledFeatures);
    virtual ~Solver() {}

    virtual SolutionPtr solve(PathConditionPtr pc, FormRestrictions formRestrictions, DomSnapshotStoragePtr domSnapshots, ReachablePathsConstraintSet reachablePaths, ConcolicVariableRenamerPtr renamer) = 0;
    // N.B. pc is the only mandatory parameter. The others are used in various modes to add extra features, and can be null otherwise.

    virtual QString getLastConstraintID() { return ""; }

    static QSharedPointer<Solver> getSolver(const Options& options);

protected:
    // Benchmarking
    ConcolicBenchmarkFeatures mDisabledFeatures;
};

typedef QSharedPointer<Solver> SolverPtr;

}

#endif // SOLVER_H
