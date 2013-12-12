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
#include <errno.h>

#include <QDebug>
#include <QDir>
#include <QString>

#include "statistics/statsstorage.h"

#include "concolic/solver/constraintwriter/z3str.h"

#include "z3solver.h"

namespace artemis
{

Z3Solver::Z3Solver(): Solver() {

}

SolutionPtr Z3Solver::solve(PathConditionPtr pc)
{
    std::ofstream constraintLog("/tmp/z3constraintlog", std::ofstream::out | std::ofstream::app);

    // 1. translate pc to something solvable using the translator

    Z3STRConstraintWriterPtr cw = Z3STRConstraintWriterPtr(new Z3STRConstraintWriter());

    if (!cw->write(pc, "/tmp/z3input")) {
        statistics()->accumulate("Concolic::Solver::ConstraintsNotWritten", 1);
        constraintLog << "Could not translate the PC into solver input." << std::endl << std::endl;
        return SolutionPtr(new Solution(false, false));
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsWritten", 1);

    // 2. run the solver on the file

    // TODO we could use the direct C++ solver interface and omit the system calls and file read/write

    char* artemisdir;
    artemisdir = std::getenv("ARTEMISDIR");

    if (artemisdir == NULL) {
        qDebug() << "Warning, ARTEMISDIR environment variable not set!";
        constraintLog << "Not running due to ARTEMISDIR environmaent variable not being set." << std::endl << std::endl;
        return SolutionPtr(new Solution(false, false));
    }

    QDir solverpath = QDir(QString(artemisdir));

    if (!solverpath.cd("contrib") || !solverpath.cd("Z3-str") || !solverpath.exists("Z3-str.py")) {
        qDebug() << "Warning, could not find Z3-str.py";
        constraintLog << "Could not find Z3-str.py." << std::endl << std::endl;
        return SolutionPtr(new Solution(false, false));
    }

    std::string cmd = solverpath.filePath("Z3-str.py").toStdString() + " /tmp/z3input > /tmp/z3result";
    int result = std::system(cmd.data());

    if (result != 0) {
        if(result == -1){
            constraintLog << "Call to std::system(Z3-str.py) failed with error " << errno << ": " << strerror(errno) << std::endl << std::endl;
        }else{
            constraintLog << "Call to Z3-str.py returned code " << result << "." << std::endl << std::endl;
        }
        statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);
        return SolutionPtr(new Solution(false, false));
    }

    // 3. interpret the result

    SolutionPtr solution = SolutionPtr(new Solution(true, false));
    if (solution->isSolved()) {

    }

    std::string line;
    std::ifstream fp("/tmp/z3result");

    if (fp.is_open()) {
        statistics()->accumulate("Concolic::Solver::ConstraintsSolved", 1);

        std::getline(fp, line); // discard decoractive line
        std::getline(fp, line); // load sat line

        if (line.compare(">> SAT") != 0) {
            // UNSAT
            statistics()->accumulate("Concolic::Solver::ConstraintsSolvedAsUNSAT", 1);
            constraintLog << "Solved as UNSAT." << std::endl << std::endl;
            return SolutionPtr(new Solution(false, true));
        }

        std::getline(fp, line); // discard decoractive line

        constraintLog << "Solved as:\n";

        while (fp.good()) {

            // split each line
            std::getline(fp, line);

            // check for end-of-solutions
            if (line.compare("************************") == 0) {
                break;
            }

            std::string symbol;
            std::string delim;
            std::string value;

            std::stringstream lines(line);
            std::getline(lines, symbol, ' ');
            std::getline(lines, delim, ' ');
            std::getline(lines, value, '\n');

            // decode type of value
            Symbolvalue symbolvalue;
            symbolvalue.found = true;

            // Empty string is signalled by the solver script as the literal ""
            // This means we cannot inject the literal "" (i.e. two double quotes) now.
            if(value.compare("\"\"") == 0){
                value.clear();
            }

            /*if (value.compare("false") == 0) {
                symbolvalue.kind = Symbolic::BOOL;
                symbolvalue.u.boolean = false;

            } else if (value.compare("true") == 0) {
                symbolvalue.kind = Symbolic::BOOL;
                symbolvalue.u.boolean = true;

            } else {
                symbolvalue.kind = Symbolic::INT;
                symbolvalue.u.integer = std::atoi(value.c_str());
            }*/

            // TODO, add support for the other types,
            // right now not needed as we only have symbolic strings as input

            symbolvalue.kind = Symbolic::STRING;

            if (value.find("(- ") == std::string::npos) { // not a negative value
                symbolvalue.string = value;
            } else {
                symbolvalue.string = "-" + value.substr(3, value.length() - 4);
            }

            // save result
            solution->insertSymbol(Z3STRConstraintWriter::decodeIdentifier(symbol).c_str(), symbolvalue);

            constraintLog << symbol << " = " << symbolvalue.string << "\n";
        }
    }else{
        statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);
        constraintLog << "Could not read result file." << std::endl << std::endl;
        return SolutionPtr(new Solution(false, false));
    }

    constraintLog << std::endl;
    constraintLog.close();
    fp.close();

    return solution;

}

} // namespace artemis
