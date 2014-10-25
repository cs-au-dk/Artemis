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

#include "solver.h"

#include "z3solver.h"
#include "kaluzasolver.h"
#include "cvc4solver.h"

namespace artemis
{

Solver::Solver(ConcolicBenchmarkFeatures disabledFeatures)
    : mDisabledFeatures(disabledFeatures)
{
}


QSharedPointer<Solver> Solver::getSolver(const Options& options)
{
    switch(options.solver) {
    case Z3STR:
        return Z3SolverPtr(new Z3Solver(options.concolicDisabledFeatures));
    case KALUZA:
        return KaluzaSolverPtr(new KaluzaSolver(options.concolicDisabledFeatures));
    case CVC4:
        return CVC4SolverPtr(new CVC4Solver(options.concolicDisabledFeatures));
    default:
        std::cerr << "Unknown solver selected" << std::endl;
        exit(1);
    }
}


} // namespace artemis
