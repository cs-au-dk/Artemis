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

#include <QDir>
#include <QString>
#include <QDateTime>

#include "statistics/statsstorage.h"

#include "concolic/solver/constraintwriter/cvc4.h"

#include "cvc4solver.h"

namespace artemis
{

CVC4Solver::CVC4Solver()
    : Solver()
{
}

CVC4Solver::~CVC4Solver()
{
}

SolutionPtr CVC4Solver::emitError(std::ofstream& clog, const std::string& reason)
{
    clog << "ERROR: " << reason << std::endl << std::endl;

    return SolutionPtr(new Solution(false, false, QString::fromStdString(reason)));
}

void CVC4Solver::emitConstraints(std::ofstream& constraintIndex, const QString& identifier, bool sat)
{
    constraintIndex << identifier.toStdString() << "," << (sat ? "sat/unknown" : "unsat") << std::endl;
    QFile::copy("/tmp/cvc4input", QString::fromStdString("/tmp/constraints/") + identifier);
}

SolutionPtr CVC4Solver::solve(PathConditionPtr pc, FormRestrictions formRestrictions)
{
    // 0. Emit debug information

    QDir().mkdir("/tmp/constraints/");
    QDir constraintsPath = QDir("/tmp/constraints/");

    QString identifier = QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss");

    int next = 0;
    while (constraintsPath.exists(identifier)) {
        if (identifier.contains("--")) {
            identifier.chop(identifier.size() - identifier.indexOf("--"));
        }

        identifier = identifier + QString("--") + QString::number(next++);
    }

    std::ofstream clog("/tmp/constraintlog", std::ofstream::out | std::ofstream::app);
    std::ofstream constraintIndex("/tmp/constraintindex", std::ofstream::out | std::ofstream::app);

    clog << "********************************************************************************" << std::endl;
    clog << "Identifier " << identifier.toStdString() << std::endl;
    clog << "Time: " << QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss").toStdString() << std::endl;
    clog << "PC: " << pc->toStatisticsValuesString(true) << std::endl;
    clog << std::endl;

    // 1. translate pc to something solvable using the translator

    CVC4ConstraintWriterPtr cw = CVC4ConstraintWriterPtr(new CVC4ConstraintWriter());

    if (!cw->write(pc, formRestrictions, "/tmp/cvc4input")) {

        statistics()->accumulate("Concolic::Solver::ConstraintsNotWritten", 1);

        std::stringstream reason;
        reason << "Could not translate the PC into solver input: " << cw->getErrorReason();
        return emitError(clog, reason.str());
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsWritten", 1);

    // 2. run the solver on the file

    char* artemisdir;
    artemisdir = std::getenv("ARTEMISDIR");

    if (artemisdir == NULL) {
        return emitError(clog, "Warning, ARTEMISDIR environment variable not set!");
    }

    QDir solverpath = QDir(QString(artemisdir));
    QString exec = "cvc4-2014-03-01-x86_64-linux-opt";

    if (!solverpath.cd("contrib") || !solverpath.cd("CVC4") || !solverpath.exists(exec)) {
        return emitError(clog, "Could not find CVC4 binary.");
    }

    // --rewrite-divk enables div and mod by a constant factor
    std::string cmd = solverpath.filePath(exec).toStdString() + " --lang=smtlib2 /tmp/cvc4input --rewrite-divk > /tmp/cvc4result 2> /tmp/cvc4result";
    std::system(cmd.data()); // result of command interpreted in step 3
    // We do not check the return code as it will be an "error" in unsat cases. Error checking is done below.

    // 3. interpret the result

    SolutionPtr solution = SolutionPtr(new Solution(true, false));

    std::string line;
    std::ifstream fp("/tmp/cvc4result");

    if (!fp.is_open()) {
        statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);
        return emitError(clog, "Could not read result file.");
    }

    statistics()->accumulate("Concolic::Solver::ConstraintsSolved", 1);

    std::getline(fp, line); // load sat line

    if (line.compare("unsat") == 0) {

        // UNSAT
        emitConstraints(constraintIndex, identifier, false);

        statistics()->accumulate("Concolic::Solver::ConstraintsSolvedAsUNSAT", 1);
        clog << "Solved as UNSAT." << std::endl << std::endl;
        return SolutionPtr(new Solution(false, true));

    } else if (line.compare("sat") != 0 && line.compare("unknown") != 0) {

        // ERROR, we can't use return types to detect errors, since an unsat result will result in an error code (because we try to access the model)

        statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);

        // Copy contents of constraint files for debugging

        clog << "Constraints:" << std::endl << std::endl;

        std::ifstream fp_input;
        fp_input.open ("/tmp/cvc4input");
        std::string line;
        while (std::getline(fp_input, line)) {
            clog << line << std::endl;
        }
        fp_input.close();

        clog << "Result: " << std::endl;

        std::ifstream fp_result;
        fp_result.open ("/tmp/cvc4result");
        while (std::getline(fp_result, line)) {
            clog << line << std::endl;
        }
        fp_result.close();

        clog << std::endl;

        fp.close(); // The main fp.

        return emitError(clog, "CVC4 responded with an error while solving the constraints.");
    }

    // Notice, we interpret sat and unknown internally as sat

    emitConstraints(constraintIndex, identifier, true);

    std::getline(fp, line); // discard model line

    clog << "Solved as:\n";

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

        // The variable names indicate the type of the variable when it was read from the DOM.
        // SYM_IN_x => string, SYM_IN_INT_y => int, SYM_IN_BOOL_z => bool
        // But we also have the type used by the solver for that variable. These should walways match up, except in
        // the case where we perform a string->int optimisation and see a string named variable with int type in the
        // solver. These variables should be converted back to strings.

        Symbolic::Type symbol_name_type;
        if (SMTConstraintWriter::decodeIdentifier(symbol).compare(0, 12, "SYM_IN_BOOL_") == 0) {
            symbol_name_type = Symbolic::BOOL;
        } else if (SMTConstraintWriter::decodeIdentifier(symbol).compare(0, 11, "SYM_IN_INT_") == 0) {
            symbol_name_type = Symbolic::INT;
        } else {
            symbol_name_type = Symbolic::STRING;
        }

        if (type.compare("String") == 0) {
            // Double-check we have a string-typed variable name.
            if (symbol_name_type != Symbolic::STRING){
                return emitError(clog, "Variable name and type mismatch for String variable in solver's result.");
            }

            symbolvalue.kind = Symbolic::STRING;

            // Strip quotes from strings
            // TODO: Does this even need to be conditional, can strings be returned without quotes?
            if (value.find("\"") != std::string::npos && value.length() > 1) {
                value = value.substr(1, value.length() - 2);
            }

            symbolvalue.string = value;

        } else if (type.compare("Bool") == 0) {
            // Double-check we have a bool-typed variable name.
            if (symbol_name_type != Symbolic::BOOL){
                return emitError(clog, "Variable name and type mismatch for Bool variable in solver's result.");
            }

            symbolvalue.kind = Symbolic::BOOL;

            if (value.compare("false") == 0) {
                symbolvalue.u.boolean = false;
            } else if (value.compare("true") == 0) {
                symbolvalue.u.boolean = true;
            } else {
                return emitError(clog, "Value of boolean returned is not true/false.");
            }

        } else if (type.compare("Int") == 0) {
            // Check the type according to the variable name.
            if (symbol_name_type == Symbolic::INT) {
                // This really is an int-typed variable.

                symbolvalue.kind = Symbolic::INT;

                // Handle negative values.
                if (value.find("(- ") == std::string::npos) {
                    std::stringstream(value) >> symbolvalue.u.integer;
                } else {
                    std::stringstream(value.substr(3, value.length() - 3)) >> symbolvalue.u.integer;
                    symbolvalue.u.integer *= -1;
                }

            } else if (symbol_name_type == Symbolic::STRING) {
                // This variable was optimised string->int by the constraint writer to help CVC4.
                // We want to undo this here.

                symbolvalue.kind = Symbolic::STRING;

                // Handle negative values.
                if (value.find("(- ") == std::string::npos) {
                    symbolvalue.string = value;
                } else {
                    symbolvalue.string = "-" + value.substr(3, value.length() - 3);
                }
            } else {
                return emitError(clog, "Variable name and type mismatch for Int variable in solver's result.");
            }


        } else {
            std::ostringstream err;
            err << "Unknown type " << type << " encountered in result.";
            return emitError(clog, err.str());
        }

        // save result
        solution->insertSymbol(SMTConstraintWriter::decodeIdentifier(symbol).c_str(), symbolvalue);

        clog << symbol << " = " << symbolvalue.string << std::endl;
    }

    clog << std::endl;
    clog.close();
    constraintIndex.close();

    fp.close();

    return solution;
}

} // namespace artemis
