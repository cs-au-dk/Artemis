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

#include "concolic/solver/constraintwriter/cvc4.h"

#include "cvc4solver.h"

namespace artemis
{

CVC4Solver::CVC4Solver(): Solver() {

}

SolutionPtr CVC4Solver::solve(PathConditionPtr pc)
{
    std::ofstream constraintLog("/tmp/constraintlog", std::ofstream::out | std::ofstream::app);

    // 1. translate pc to something solvable using the translator

    CVC4ConstraintWriterPtr cw = CVC4ConstraintWriterPtr(new CVC4ConstraintWriter());

    if (!cw->write(pc, "/tmp/cvc4input")) {
        statistics()->accumulate("Concolic::Solver::ConstraintsNotWritten", 1);
        constraintLog << "Could not translate the PC into solver input." << std::endl << std::endl;
        return SolutionPtr(new Solution(false, false));
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsWritten", 1);

    // 2. run the solver on the file

    // TODO we could use the direct C++ solver interface and omit the system calls and file read/write

    // --rewrite-divk enables div and mod by a constant factor
    std::string cmd = "cvc4 --lang=smtlib2 /tmp/cvc4input --rewrite-divk > /tmp/cvc4result";
    int result = std::system(cmd.data());

    if (result != 0) {
        if(result == -1){
            constraintLog << "Call to std::system(cvc4) failed with error " << errno << ": " << strerror(errno) << std::endl << std::endl;
        }else{
            constraintLog << "Call to cvc4 returned code " << result << "." << std::endl << std::endl;
        }
        statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);
        return SolutionPtr(new Solution(false, false));
    }

    // 3. interpret the result

    SolutionPtr solution = SolutionPtr(new Solution(true, false));

    std::string line;
    std::ifstream fp("/tmp/cvc4result");

    if (fp.is_open()) {
        statistics()->accumulate("Concolic::Solver::ConstraintsSolved", 1);

        std::getline(fp, line); // load sat line

        if (line.compare("sat") != 0) {
            // UNSAT
            statistics()->accumulate("Concolic::Solver::ConstraintsSolvedAsUNSAT", 1);
            constraintLog << "Solved as UNSAT." << std::endl << std::endl;
            return SolutionPtr(new Solution(false, true));
        }

        std::getline(fp, line); // discard model line

        constraintLog << "Solved as:\n";

        while (fp.good()) {

            // split each line
            std::getline(fp, line);

            // check for end-of-solutions
            if (line.compare(")") == 0) {
                break;
            }

            std::string symbol;
            std::string type;
            std::string value;

            std::stringstream ss(line);
            std::getline(ss, symbol, ' '); // skip a static prefix
            std::getline(ss, symbol, ' ');
            std::getline(ss, type, ' '); // skip a static prefix
            std::getline(ss, type, ' ');

            if (type.compare("String") == 0) {
                std::getline(ss, value, ' '); // skip redundant "type" string
            }

            std::getline(ss, value, ')');

            // decode type of value
            Symbolvalue symbolvalue;
            symbolvalue.found = true;

            // Empty string is signalled by the solver script as the literal ""
            // This means we cannot inject the literal "" (i.e. two double quotes) now.
            if (value.compare("\"\"") == 0){
                value.clear();
            }

            // Strip quotes from strings
            if (type.compare("String") == 0 && value.find("\"") != std::string::npos && value.length() > 1) {
                value = value.substr(1, value.length() - 2);
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
                symbolvalue.string = "-" + value.substr(3, value.length() - 3);
            }

            // save result
            solution->insertSymbol(SMTConstraintWriter::decodeIdentifier(symbol).c_str(), symbolvalue);

            constraintLog << symbol << " = " << symbolvalue.string << "\n";
        }
    } else {
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
