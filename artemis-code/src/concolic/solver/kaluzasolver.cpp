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

#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sstream>

#include <QDebug>
#include <QDir>
#include <QString>

#include "statistics/statsstorage.h"

#include "concolic/solver/constraintwriter/kaluza.h"

#include "kaluzasolver.h"

namespace artemis
{

KaluzaSolver::KaluzaSolver(ConcolicBenchmarkFeatures disabledFeatures)
    : Solver(disabledFeatures)
{
}

SolutionPtr KaluzaSolver::solve(PathConditionPtr pc, FormRestrictions formRestrictions, DomSnapshotStorage domSnapshots)
{
    qDebug() << "Warning: KaluzaSolver does not support implicit form restrictions.\n";

    // 1. translate pc to something solvable using the translator

    KaluzaConstraintWriterPtr constraintwriter = KaluzaConstraintWriterPtr(new KaluzaConstraintWriter());

    if (!constraintwriter->write(pc, formRestrictions, domSnapshots, "/tmp/kaluza")) {
        Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsNotWritten", 1);
        return SolutionPtr(new Solution(false, false));
    }

    Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsWritten", 1);

    // 2. run the solver on the file

    char* artemisdir;
    artemisdir = std::getenv("ARTEMISDIR");

    if (artemisdir == NULL) {
        qDebug() << "Warning, ARTEMISDIR environment variable not set!";
        return SolutionPtr(new Solution(false, false));
    }

    QDir solverpath = QDir(QString(artemisdir));

    if (!solverpath.cd("contrib") || !solverpath.cd("Kaluza") || !solverpath.exists("artemiskaluza.sh")) {
        qDebug() << "Warning, could not find artemiskaluza.sh";
        return SolutionPtr(new Solution(false, false));
    }

    int result = std::system(solverpath.filePath("artemiskaluza.sh").toStdString().data());

    if (result != 0) {
        Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);
        return SolutionPtr(new Solution(false, false));
    }

    Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsSolved", 1);

    // 3. interpret the result

    SolutionPtr solution = SolutionPtr(new Solution(true, false));
    if (solution->isSolved()) {

    }

    std::string line;
    std::ifstream fp("/tmp/kaluza-result");

    if (fp.is_open()) {
        while (fp.good()) {

            // split each line
            std::getline(fp, line);

            std::string symbol;
            std::string value;

            std::stringstream lines(line);
            std::getline(lines, symbol, ' ');
            std::getline(lines, value, ' ');

            if (symbol.compare("") == 0) {
                continue; // ignore blank lines
            }

            // decode type of value
            Symbolvalue symbolvalue;
            symbolvalue.found = true;

            if (value.compare("false") == 0) {
                symbolvalue.kind = Symbolic::BOOL;
                symbolvalue.u.boolean = false;

            } else if (value.compare("true") == 0) {
                symbolvalue.kind = Symbolic::BOOL;
                symbolvalue.u.boolean = true;

            } else {
                symbolvalue.kind = Symbolic::INT;
                symbolvalue.u.integer = std::atoi(value.c_str());
            }

            // TODO add string support

            // save result
            solution->insertSymbol(symbol.c_str(), symbolvalue);
        }
    }

    fp.close();

    return solution;

}

} // namespace artemis
