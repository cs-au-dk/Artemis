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

#ifndef CVC4SOLVER_H
#define CVC4SOLVER_H

#include "solver.h"

#include <QString>

namespace artemis
{

/*
 *  Generic symbolic constrint solver interface.
 */

class CVC4Solver : public Solver
{
public:

    CVC4Solver();
    ~CVC4Solver();

    SolutionPtr solve(PathConditionPtr pc);

private:
    SolutionPtr emitError(std::ofstream& clog, const std::string& reason);
    void emitConstraints(std::ofstream& constraintIndex, const QString& identifier, bool sat);

};

typedef QSharedPointer<CVC4Solver> CVC4SolverPtr;

}

#endif // CVC4SOLVER_H
