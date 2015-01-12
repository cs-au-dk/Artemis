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
#include <QElapsedTimer>

#include "concolic/solver/constraintwriter/cvc4.h"

#include "statistics/statsstorage.h"

#include "cvc4solver.h"

namespace artemis
{

CVC4Solver::CVC4Solver(ConcolicBenchmarkFeatures disabledFeatures)
    : Solver(disabledFeatures)
{
}

CVC4Solver::~CVC4Solver()
{
}

SolutionPtr CVC4Solver::solve(PathConditionPtr pc, FormRestrictions formRestrictions, DomSnapshotStorage domSnapshots)
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
    mLastConstraintID = identifier;

    std::ofstream clog("/tmp/constraintlog", std::ofstream::out | std::ofstream::app);
    std::ofstream constraintIndex("/tmp/constraintindex", std::ofstream::out | std::ofstream::app);

    Log::info(QString("  Constraint file: %1").arg(identifier).toStdString());

    clog << "********************************************************************************" << std::endl;
    clog << "Identifier " << identifier.toStdString() << std::endl;
    clog << "Time: " << QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss").toStdString() << std::endl;
    clog << "PC: " << pc->toStatisticsValuesString(true) << std::endl;
    clog << std::endl;

    // 1. translate pc to something solvable using the translator

    CVC4ConstraintWriterPtr cw = CVC4ConstraintWriterPtr(new CVC4ConstraintWriter(mDisabledFeatures));

    if (!cw->write(pc, formRestrictions, domSnapshots, "/tmp/cvc4input")) {

        Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsNotWritten", 1);

        std::stringstream reason;
        reason << "Could not translate the PC into solver input: " << cw->getErrorReason();
        return emitError(clog, reason.str(), cw->getErrorClause());

    }

    Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsWritten", 1);

    // 2. run the solver on the file

    char* artemisdir;
    artemisdir = std::getenv("ARTEMISDIR");

    if (artemisdir == NULL) {
        return emitError(clog, "Warning, ARTEMISDIR environment variable not set!");
    }

    QDir solverpath = QDir(QString(artemisdir));
    QString exec = "timed-cvc4.sh";

    if (!solverpath.cd("contrib") || !solverpath.cd("CVC4") || !solverpath.exists(exec)) {
        return emitError(clog, "Could not find CVC4 binary.");
    }

    Log::info("Solving...");
    QElapsedTimer timer;

    // --rewrite-divk enables div and mod by a constant factor
    std::string cmd = solverpath.filePath(exec).toStdString() + " /tmp/cvc4input > /tmp/cvc4result 2> /tmp/cvc4result";
    timer.start();
    int result = std::system(cmd.data()); // result of command interpreted in step 3
    // We cannot use the return code for error checking as it will be an "error" in all unsat cases (because we try to get the model). Error checking is done below.
    // However we can use it to check whether the timeout script had to kill CVC4 or not.

    double time = (double)timer.elapsed()/1000;
    Log::info(QString("  Took %1s").arg(time).toStdString());
    Statistics::statistics()->accumulate("Concolic::Solver::TotalSolverTime", time);
    clog << "Duration: " << time << "s" << std::endl;

    if (WEXITSTATUS(result) == 124) {
        Statistics::statistics()->accumulate("Concolic::Solver::SolverTimeouts", 1);
        return emitError(clog, "CVC4 execution timed-out..");
    }

    // 3. interpret the result

    SolutionPtr solution = SolutionPtr(new Solution(true, false));

    std::string line;
    std::ifstream fp("/tmp/cvc4result");

    if (!fp.is_open()) {
        Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);
        return emitError(clog, "Could not read result file.");
    }

    Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsSolved", 1);

    std::getline(fp, line); // load sat line

    if (line.compare("unsat") == 0) {

        // UNSAT
        emitConstraints(constraintIndex, identifier, false);

        Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsSolvedAsUNSAT", 1);
        clog << "Solved as UNSAT." << std::endl << std::endl;
        return SolutionPtr(new Solution(false, true));

    } else if (line.compare("sat") != 0 && line.compare("unknown") != 0) {

        // ERROR, we can't use return types to detect errors, since an unsat result will result in an error code (because we try to access the model)

        Statistics::statistics()->accumulate("Concolic::Solver::ConstraintsNotSolved", 1);

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
        // SYM_IN_x => string, SYM_IN_INT_y => int, SYM_IN_BOOL_z => bool, SYM_TARGET => DOM NODE
        // But we also have the type used by the solver for that variable. These should walways match up, except in
        // the case where we perform a string->int optimisation and see a string named variable with int type in the
        // solver. These variables should be converted back to strings.

        // Variables not prefixed with SYM_ are ignored

        std::string identifier = SMTConstraintWriter::decodeIdentifier(symbol);

        if (identifier.compare(0, 7, "SYM_IN_") == 0) {
            SolutionPtr ret = decodeDOMInputResult(clog, identifier, type, value, &symbolvalue, formRestrictions);
            if (!ret.isNull()) return ret;

        } else if (identifier.compare(0, 11, "SYM_TARGET_") == 0 && identifier.find("_SOLUTIONXPATH") != std::string::npos) {
            // solution for SYM_TARGET_XX is found in SYM_TARGET_XX_SOLUTIONXPATH
            identifier = identifier.substr(0, identifier.length()-14); // remove _solutionxpath

            symbolvalue.kind = Symbolic::OBJECT;
            value = value.substr(1, value.length() - 2); // Strip quotes from strings
            symbolvalue.string = value;
        } else {
            continue;
        }

        // save result
        solution->insertSymbol(identifier.c_str(), symbolvalue);

        switch(symbolvalue.kind) {
        case Symbolic::STRING:
            clog << symbol << " = \"" << symbolvalue.string << "\"" << std::endl;
            break;
        case Symbolic::INT:
            clog << symbol << " = " << symbolvalue.u.integer << std::endl;
            break;
        case Symbolic::BOOL:
            clog << symbol << " = " << symbolvalue.u.boolean << std::endl;
            break;
        case Symbolic::OBJECT:
            clog << symbol << " is xpath[" << symbolvalue.string << "]" << std::endl;
        default:
            break;
        }
    }

    clog << std::endl;
    clog.close();
    constraintIndex.close();

    fp.close();

    return solution;
}

SolutionPtr CVC4Solver::decodeDOMInputResult(std::ofstream& clog,
                                             std::string identifier,
                                             std::string type,
                                             std::string value,
                                             Symbolvalue* symbolvalue,
                                             const FormRestrictions& formRestrictions)
{

    Symbolic::Type symbol_name_type;
    if (identifier.compare(0, 12, "SYM_IN_BOOL_") == 0) {
        symbol_name_type = Symbolic::BOOL;
    } else if (identifier.compare(0, 11, "SYM_IN_INT_") == 0) {
        symbol_name_type = Symbolic::INT;
    } else if (identifier.compare(0, 12, "SYM_IN_BOOL_")) {
        symbol_name_type = Symbolic::STRING;
    } else {
        std::cerr << "ERROR: Unknown symbol in solution: " << identifier << std::endl;
        exit(1);
    }

    if (type.compare("String") == 0) {
        // Double-check we have a string-typed variable name.
        if (symbol_name_type != Symbolic::STRING){
            Statistics::statistics()->accumulate("Concolic::Solver::ErrorsReadingSolution", 1);
            return emitError(clog, "Variable name and type mismatch for String variable in solver's result.");
        }

        symbolvalue->kind = Symbolic::STRING;

        // Strip quotes from strings
        // TODO: Does this even need to be conditional, can strings be returned without quotes?
        if (value.find("\"") != std::string::npos && value.length() > 1) {
            value = value.substr(1, value.length() - 2);
        }

        symbolvalue->string = value;

    } else if (type.compare("Bool") == 0) {
        // Double-check we have a bool-typed variable name.
        if (symbol_name_type != Symbolic::BOOL){
            Statistics::statistics()->accumulate("Concolic::Solver::ErrorsReadingSolution", 1);
            return emitError(clog, "Variable name and type mismatch for Bool variable in solver's result.");
        }

        symbolvalue->kind = Symbolic::BOOL;

        if (value.compare("false") == 0) {
            symbolvalue->u.boolean = false;
        } else if (value.compare("true") == 0) {
            symbolvalue->u.boolean = true;
        } else {
            Statistics::statistics()->accumulate("Concolic::Solver::ErrorsReadingSolution", 1);
            return emitError(clog, "Value of boolean returned is not true/false.");
        }

    } else if (type.compare("Int") == 0) {
        // Check the type according to the variable name.
        if (symbol_name_type == Symbolic::INT) {
            // This really is an int-typed variable.

            symbolvalue->kind = Symbolic::INT;

            // Handle negative values.
            if (value.find("(- ") == std::string::npos) {
                std::stringstream(value) >> symbolvalue->u.integer;
            } else {
                std::stringstream(value.substr(3, value.length() - 3)) >> symbolvalue->u.integer;
                symbolvalue->u.integer *= -1;
            }

        } else if (symbol_name_type == Symbolic::STRING) {
            // This variable was optimised string->int by the constraint writer to help CVC4.
            // We want to undo this here.

            symbolvalue->kind = Symbolic::STRING;

            // Handle negative values.
            if (value.find("(- ") == std::string::npos) {
                symbolvalue->string = value;
            } else {
                symbolvalue->string = "-" + value.substr(3, value.length() - 3);
            }

            // If the symbol references a select element, then we must ensure that
            // the solved value matches a valid value for the select.
            // This is not always the case if leading zeros exist in the select, since
            // these are stripped out in our solution.

            if (FormFieldRestrictedValues::symbolReferencesSelect(formRestrictions, QString::fromStdString(identifier))) {

                if (FormFieldRestrictedValues::isValidSelectValue(formRestrictions, QString::fromStdString(identifier), QString::fromStdString(symbolvalue->string)) ||
                    FormFieldRestrictedValues::fuzzyMatchSelectValue(formRestrictions, QString::fromStdString(identifier), &symbolvalue->string)) {

                    // either it was valid, or fuzzyMatch found a match and updated the value for us

                } else {
                    Statistics::statistics()->accumulate("Concolic::Solver::InvalidSolution", 1);
                    return emitError(clog, "Solver returned a solution which is invalid according to the form restrictions.");

                }

            }

        }  else {
            Statistics::statistics()->accumulate("Concolic::Solver::ErrorsReadingSolution", 1);
            return emitError(clog, "Variable name and type mismatch for Int variable in solver's result.");
        }


    } else {
        Statistics::statistics()->accumulate("Concolic::Solver::ErrorsReadingSolution", 1);
        std::ostringstream err;
        err << "Unknown type " << type << " encountered in result.";
        return emitError(clog, err.str());
    }

    return SolutionPtr(NULL);
}

SolutionPtr CVC4Solver::emitError(std::ofstream& clog, const std::string& reason, int clause)
{
    clog << "ERROR: " << reason << std::endl << std::endl;

    return SolutionPtr(new Solution(false, false, QString::fromStdString(reason), clause));
}

void CVC4Solver::emitConstraints(std::ofstream& constraintIndex, const QString& identifier, bool sat)
{
    constraintIndex << identifier.toStdString() << "," << (sat ? "sat/unknown" : "unsat") << std::endl;
    QFile::copy("/tmp/cvc4input", QString::fromStdString("/tmp/constraints/") + identifier);
}

} // namespace artemis
