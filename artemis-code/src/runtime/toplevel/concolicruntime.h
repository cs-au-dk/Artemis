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

#ifndef CONCOLICRUNTIME_H
#define CONCOLICRUNTIME_H

#include <QObject>

#include "concolic/executiontree/tracenodes.h"
#include "concolic/search/searchdfs.h"
#include "concolic/solver/solver.h"
#include "concolic/entrypoints.h"
#include "concolic/mockentrypointdetector.h"
#include "concolic/executiontree/traceprinter.h"
#include "concolic/executiontree/tracedisplay.h"
#include "concolic/executiontree/tracedisplayoverview.h"
#include "concolic/traceclassifier.h"
#include "concolic/tracestatistics.h"

#include "runtime/input/dominput.h"
#include "runtime/input/events/mouseeventparameters.h"
#include "strategies/inputgenerator/targets/legacytarget.h"
#include "runtime/input/clickinput.h"
#include "runtime/browser/artemiswebview.h"
#include "runtime/input/forms/injectionvalue.h"
#include "runtime/input/forms/formfieldinjector.h"

#include "runtime/runtime.h"

namespace artemis
{

/*
 *  The main controller for the concolic execution.
 *
 *  Algorithm:
 *      Insert "default" input as next input
 *      While next input exists do:
 *          Execute WebKit using the next input
 *          Merge the last execution trace with the symbolic execution tree
 *          Search algorithm chooses a desired path
 *          Retrieve the coresponding path constraint (from path tree)
 *          Solve the constraint, returns a concrete input to test
 *              * Need to deal with cases where we can't solve (simplest implementation: mark as given up and move on)
 *          Set next input according to the result of the constraint solver
 *      od
 *
 *  Steps that needs to be added (formcrawl project):
 *
 *    Build an annotated trace of the path taken
 *    Classify the trace as a success/failure and add it to the tree
 *    Check that we took the intended path
 *      * Need to deal with cases where we did not (simplest implementation: just give up)
 *    Finish after some condition (coverage, timeout, ...)
 *
 *  We also have a demo mode which does not drive the execution but only records and prints out the information
 *  which would be collected during a run of concolic execution.
 *
 */
class ConcolicRuntime : public Runtime
{
    Q_OBJECT

public:
    ConcolicRuntime(QObject* parent, const Options& options, const QUrl& url);

    void run(const QUrl& url);
    void done();

protected:
    void preConcreteExecution();

    QUrl mUrl;

    ArtemisWebViewPtr mWebView;

    QSharedPointer<ExecutableConfiguration> mNextConfiguration;
    TraceNodePtr mSymbolicExecutionGraph;
    EventHandlerDescriptorConstPtr mEntryPointEvent;

    bool mRunningFirstLoad;
    bool mRunningWithInitialValues;

    // Controls for the search procedure.
    DepthFirstSearchPtr mSearchStrategy; // TODO: For now we are using DFS hard-coded...
    int mSearchPasses; // The number of passes to make of the search algorithm before giving up.
    bool mSearchPassesUnlimited; // Whether to limit the number of passes we do at all. If true, we search until there are no unexplored nodes remaining.
    bool mSearchFoundTarget;

    // For now, we can choose between entry points specified by XPath (with --concolic-button) or the built-in EP finding.
    // If an XPath has been give, we want to skip the entry point finding run completely and use a different method for injecting clicks.
    // If mManualEntryPoint is set, then we use mEntryPointXPath and skip the first iteration, otherwise we use mEntryPointEvent.
    bool mManualEntryPoint;
    QString mManualEntryPointXPath;

    TraceClassifier mTraceClassifier;

    // Method and variables for generating a graphviz graph of the execution tree.
    void outputTreeGraph();
    TraceDisplay mTraceDisplay;
    TraceDisplayOverview mTraceDisplayOverview;
    QString mGraphOutputNameFormat;
    int mGraphOutputIndex;
    QString mGraphOutputPreviousName;
    QString mGraphOutputOverviewPreviousName;

    // Helper methods for postConcreteExecution.
    void setupNextConfiguration(QSharedPointer<FormInputCollection> formInput);
    void postInitialConcreteExecution(QSharedPointer<ExecutionResult> result);
    void mergeTraceIntoTree();
    void printSolution(SolutionPtr solution, QStringList varList);
    QSharedPointer<FormInputCollection> createFormInput(QMap<QString, Symbolic::SourceIdentifierMethod> freeVariables, SolutionPtr solution);
    QSharedPointer<const FormFieldDescriptor> findFormFieldForVariable(QString varName, Symbolic::SourceIdentifierMethod varSourceIdentifierMethod);
    void exploreNextTarget();
    void chooseNextTargetAndExplore();
    void reportStatistics();

    QList<FormFieldDescriptorConstPtr> mFormFields;

    // State
    int mNumIterations;

private slots:
    void postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result);
    void postValueInjection();

signals:
    void sigNewTraceMarker(QString label, QString index);

};

} // namespace artemis

#endif // CONCOLICRUNTIME_H
