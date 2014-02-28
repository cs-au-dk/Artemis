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
        constraintLog << "Could not translate the PC into solver input." << std::endl;
        constraintLog << pc->toStatisticsValuesString(true) << std::endl << std::endl;
        return SolutionPtr(new Solution(false, false, "Could not translate the PC into solver input."));
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsWritten", 1);

    // 2. run the solver on the file

    // TODO we could use the direct C++ solver interface and omit the system calls and file read/write

    char* artemisdir;
    artemisdir = std::getenv("ARTEMISDIR");

    if (artemisdir == NULL) {
        qDebug() << "Warning, ARTEMISDIR environment variable not set!";
        constraintLog << "Not running due to ARTEMISDIR environmaent variable not being set." << std::endl << std::endl;
        return SolutionPtr(new Solution(false, false, "Could not run solver because ARTEMISDIR is not set."));
    }

    QDir solverpath = QDir(QString(artemisdir));
    QString exec = "cvc4-2014-02-19-x86_64-linux-opt";

    if (!solverpath.cd("contrib") || !solverpath.cd("CVC4") || !solverpath.exists(exec)) {
        qDebug() << "Warning, could not find " << exec;;
        constraintLog << "Could not find " << exec.toStdString() << std::endl << std::endl;
        return SolutionPtr(new Solution(false, false, "Could not find CVC4 binary."));
    }

    // --rewrite-divk enables div and mod by a constant factor
    std::string cmd = solverpath.filePath(exec).toStdString() + " --lang=smtlib2 /tmp/cvc4input --rewrite-divk > /tmp/cvc4result 2> /tmp/cvc4result";
    std::system(cmd.data()); // result of command interpreted in step 3
    // We do not check the return code as it will be an "error" in unsat cases. Error checking is done below.

    // 3. interpret the result

    SolutionPtr solution = SolutionPtr(new Solution(true, false));

    std::string line;
    std::ifstream fp("/tmp/cvc4result");

    if (fp.is_open()) {
        statistics()->accumulate("Concolic::Solver::ConstraintsSolved", 1);

        std::getline(fp, line); // load sat line

        if (line.compare("unsat") == 0) {
            // UNSAT
            statistics()->accumulate("Concolic::Solver::ConstraintsSolvedAsUNSAT", 1);
            constraintLog << "Solved as UNSAT." << std::endl << std::endl;
            return SolutionPtr(new Solution(false, true));
        } else if (line.compare("sat") != 0 && line.compare("unknown") != 0) {
            // ERROR, we can't use return types to detect errors, since an unsat result will result in an error code (because we try to access the model)
            statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);

            constraintLog << "Error when solving the following PC:" << std::endl;

            constraintLog <<pc->toStatisticsValuesString(true);

            constraintLog << std::endl << "The input file was:" << std::endl;

            std::ifstream fp_input;
            fp_input.open ("/tmp/cvc4input");
            std::string line;
            while (std::getline(fp_input, line)) {
                constraintLog << line << std::endl;
            }
            fp_input.close();

            constraintLog << std::endl << "The result was:" << std::endl;

            // Copy /tmp/cvc4result into constraintlog using a fresh file pointer (i.e. not the one we ).
            std::ifstream fp_result;
            fp_result.open ("/tmp/cvc4result");
            while (std::getline(fp_result, line)) {
                constraintLog << line << std::endl;
            }
            fp_result.close();

            constraintLog << std::endl;

            fp.close(); // The main fp.
            return SolutionPtr(new Solution(false, false, "There was an error while running the solver."));

        }

        // Notice, we interpret sat and unknown internally as sat

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
        return SolutionPtr(new Solution(false, false, "Could not read result file."));
    }

    constraintLog << std::endl;
    constraintLog.close();
    fp.close();

    return solution;

}

} // namespace artemis
