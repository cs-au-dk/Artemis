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

#include <cstdlib>
#include <iostream>
#include <fstream>
#include <sstream>

#include <QDebug>
#include <QDir>
#include <QString>

#include "statistics/statsstorage.h"

#include "concolic/solver/constraintwriter/z3str.h"

#include "solver.h"

namespace artemis
{

SolutionPtr Solver::solve(PathConditionPtr pc)
{

    // 1. translate pc to something solvable using the translator

    ConstraintWriterPtr cw = ConstraintWriterPtr(new Z3STRConstraintWriter());

    if (!cw->write(pc, "/tmp/z3input")) {
        statistics()->accumulate("Concolic::Solver::ConstraintsNotWritten", 1);
        return SolutionPtr(new Solution(false));
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsWritten", 1);

    // 2. run the solver on the file

    // TODO we could use the direct C++ solver interface and omit the system calls and file read/write

    char* artemisdir;
    artemisdir = std::getenv("ARTEMISDIR");

    if (artemisdir == NULL) {
        qDebug() << "Warning, ARTEMISDIR environment variable not set!";
        return SolutionPtr(new Solution(false));
    }

    QDir solverpath = QDir(QString(artemisdir));

    if (!solverpath.cd("contrib") || !solverpath.cd("Z3-str") || !solverpath.exists("Z3-str.py")) {
        qDebug() << "Warning, could not find Z3-str.py";
        return SolutionPtr(new Solution(false));
    }

    std::string cmd = solverpath.filePath("Z3-str.py").toStdString() + " /tmp/z3input > /tmp/z3result";
    int result = std::system(cmd.data());

    if (result != 0) {
        statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);
        return SolutionPtr(new Solution(false));
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsSolved", 1);

    // 3. interpret the result

    SolutionPtr solution = SolutionPtr(new Solution(true));
    if (solution->isSolved()) {

    }

    std::string line;
    std::ifstream fp("/tmp/z3result");

    if (fp.is_open()) {

        std::getline(fp, line); // discard decoractive line
        std::getline(fp, line); // load sat line

        if (line.compare(">> SAT") != 0) {
            // UNSAT
            statistics()->accumulate("Concolic::Solver::ConstraintsSolvedAsUNSAT", 1);
            return SolutionPtr(new Solution(false));
        }

        std::getline(fp, line); // discard decoractive line

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
            symbolvalue.string = value;

            // save result
            solution->insertSymbol(Z3STRConstraintWriter::decodeIdentifier(symbol).c_str(), symbolvalue);
        }
    }

    fp.close();

    return solution;

}

} // namespace artemis
