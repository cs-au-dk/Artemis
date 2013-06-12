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

#include "statistics/statsstorage.h"

#include "concolic/solver/constraintwriter.h"

#include "solver.h"

namespace artemis
{

Solution Solver::solve(QSharedPointer<Symbolic::PathCondition> pc)
{

    // 1. translate pc to something solvable using the translator

    if (!ConstraintWriter::write(pc, "/tmp/kaluza")) {
        statistics()->accumulate("Concolic::Solver::ConstraintsNotWritten", 1);
        return Solution(false);
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsWritten", 1);

    // 2. run the solver on the file

    int result = std::system("/home/semadk/Downloads/KaluzaBin/artemiskaluza.sh");

    if (result != 0) {
        statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);
        return Solution(false);
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsSolved", 1);

    // 3. interpret the result

    Solution solution(true);

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
            solution.insertSymbol(symbol, symbolvalue);
        }
    }

    fp.close();

}

} // namespace artemis
