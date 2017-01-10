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

#include "concolicstandaloneruntime.h"

#include <QFileInfo>

#include "util/loggingutil.h"
#include "symbolic/directaccesssymbolicvalues.h"
#include "concolic/executiontree/tracedisplay.h"
#include "concolic/executiontree/tracedisplayoverview.h"
#include "util/fileutil.h"

namespace artemis
{


ConcolicStandaloneRuntime::ConcolicStandaloneRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
    , mConcolicAnalysis(new ConcolicAnalysis(options, ConcolicAnalysis::CONCOLIC_RUNTIME))
    , mNumIterations(0)
{
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(slExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));
}

void ConcolicStandaloneRuntime::run(const QUrl &url)
{
    mUrl = url; // Expected to be about:blank.

    // Load the JavaScript snippet to be tested
    mJsCode = loadJsSnippet();
    if (mJsCode.isNull() || mJsCode.isEmpty()) {
        Log::fatal("Error: Could not load any JavaScript code to test.");
        exit(1);
    }

    // Run the analysis
    newConcolicIteration(); // Runs until done, then calls done().
}


// Loads the JS code to be tested and returns it as a string.
QString ConcolicStandaloneRuntime::loadJsSnippet()
{
    mJsFilename = mOptions.concolicTestModeJsFile;

    if (mJsFilename.isNull() || mJsFilename.isEmpty()) {
        Log::fatal("Concolic-test mode: A JS file to test must be given with '--concolic-test-mode-js <file>'.");
        return QString();
    }

    // Check mJsFilename is a file, etc.
    QFileInfo qfi = QFileInfo(mJsFilename);
    if (!qfi.exists()) {
        Log::fatal("Concolic-test mode JS file does not exist:");
        Log::fatal(mJsFilename.toStdString());
        return QString();
    }
    if (!qfi.isFile()) {
        Log::fatal("Concolic-test mode JS file is not a file:");
        Log::fatal(mJsFilename.toStdString());
        return QString();
    }
    if (!qfi.isReadable()) {
        Log::fatal("Concolic-test mode JS file is not readable:");
        Log::fatal(mJsFilename.toStdString());
        return QString();
    }

    // Read in the JS code.
    QString jsString = readFile(mJsFilename);
    return jsString;
}



void ConcolicStandaloneRuntime::newConcolicIteration()
{
    Log::debug(QString("Concolic-test mode: Iteration %1").arg(mNumIterations+1).toStdString());

    // For each iteration we reload the page (blank) and then inject the JavaScript snippet.
    ExecutableConfigurationPtr noInput = ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), mUrl));
    mWebkitExecutor->executeSequence(noInput, MODE_CONCOLIC_NO_TRACE); // Calls slExecutedSequence method as callback.
}


void ConcolicStandaloneRuntime::slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // We have loaded the page.
    // Now, begin recording the trace and inject the JavaScript.
    mWebkitExecutor->getTraceBuilder()->beginRecording();

    // Inject
    Log::debug("Concolic-test mode: Beginning JavaScript execution.");
    //qDebug() << mJsCode;
    QVariant jsResult = mWebkitExecutor->getPage()->currentFrame()->documentElement().evaluateJavaScript(mJsCode, QUrl(), false);
    qDebug() << "Concolic-test mode: Execution result:\n" << jsResult;

    // End the trace recording and return this trace.
    mWebkitExecutor->getTraceBuilder()->endRecording();
    TraceNodePtr trace = mWebkitExecutor->getTraceBuilder()->trace();

    doneConcolicIteration(trace);
}

void ConcolicStandaloneRuntime::doneConcolicIteration(TraceNodePtr trace)
{
    // Save this trace into the tree.
    // N.B. We do not classify the traces in concolic standalone mode.
    ConcolicAnalysis::ExplorationHandle target;
    if (mNumIterations == 0) {
        // If we are on the first iteration, there was no prior exploartion target.
        target = ConcolicAnalysis::NO_EXPLORATION_TARGET;
    } else {
        target = mExplorationResult.target;
    }
    mConcolicAnalysis->addTrace(trace, target);
    concolicOutputTree();

    // Check if we have reached the iteration limit.
    mNumIterations++;
    if (mOptions.iterationLimit > 0 && mNumIterations >= mOptions.iterationLimit) {
        Log::info("Concolic-test mode: Iteration limit reached");
        done();
    }

    // Check if there are more paths to explore.
    mExplorationResult = mConcolicAnalysis->nextExploration();
    if (!mExplorationResult.newExploration) {
        Log::info("Concolic-test mode: Exhausted possible explorations.");
        done();
    }
    assert(mExplorationResult.solution->isSolved());

    // The values from mExplorationResult are saved to the direct-injection table. We do not support any other type of injection in this mode.
    Symbolic::DirectAccessSymbolicValues* symValueStore = Symbolic::get_direct_access_symbolic_values_store();
    symValueStore->reset();
    foreach (QString symbol, mExplorationResult.solution->symbols()) {
        // Remove the SYM_IN_* prefix.
        QString varName = symbol;
        varName.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

        // Check the type and save the value.
        Symbolvalue value = mExplorationResult.solution->findSymbol(symbol);
        switch (value.kind) {
        case Symbolic::STRING:
            symValueStore->setString(varName, QString::fromStdString(value.string));
            break;
        case Symbolic::INT:
            symValueStore->setInteger(varName, value.u.integer);
            break;
        case Symbolic::BOOL:
            symValueStore->setBoolean(varName, value.u.boolean);
            break;
        default:
            Log::fatal(QString("Error: Unexpected value type encountered for variable %1 (%2).").arg(symbol).arg(value.kind).toStdString());
            exit(1);
        }
    }

    // Begin a new itration with the new values.
    newConcolicIteration();
}



void ConcolicStandaloneRuntime::concolicOutputTree()
{
    int iter_id = mNumIterations + 1;
    QString jsFile = QFileInfo(mJsFilename).fileName();
    QString title = QString("%1, iteration %2").arg(jsFile).arg(iter_id);

    QString filename = QString("concolic-test-tree_%1.gv").arg(iter_id);
    QString filenameOverview = QString("concolic-test-tree_%1_overview.gv").arg(iter_id);;

    TraceDisplay display(mOptions.outputCoverage != NONE);
    TraceDisplayOverview displayOverview(mOptions.outputCoverage != NONE);

    display.writeGraphFile(mConcolicAnalysis->getExecutionTree(), filename, false, title);
    displayOverview.writeGraphFile(mConcolicAnalysis->getExecutionTree(), filenameOverview, false, title);
}


} // namespace artemis
