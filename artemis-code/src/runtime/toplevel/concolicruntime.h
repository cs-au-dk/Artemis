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

#include "concolic/concolicanalysis.h"
#include "concolic/executiontree/tracenodes.h"
#include "concolic/solver/solution.h"
#include "concolic/entrypoints.h"
#include "concolic/mockentrypointdetector.h"
#include "concolic/executiontree/traceprinter.h"
#include "concolic/executiontree/tracedisplay.h"
#include "concolic/executiontree/tracedisplayoverview.h"
#include "concolic/traceclassifier.h"
#include "concolic/tracestatistics.h"
#include "concolic/handlerdependencytracker.h"
#include "concolic/search/abstractselector.h"

#include "runtime/input/dominput.h"
#include "runtime/input/events/mouseeventparameters.h"
#include "strategies/inputgenerator/targets/legacytarget.h"
#include "runtime/input/clickinput.h"
#include "runtime/browser/artemiswebview.h"
#include "runtime/input/forms/injectionvalue.h"
#include "runtime/input/forms/formfieldinjector.h"
#include "runtime/input/forms/formfieldrestrictedvalues.h"

#include "runtime/runtime.h"

namespace artemis
{

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

    ConcolicAnalysisPtr mConcolicAnalysis;
    ConcolicAnalysis::ExplorationResult mExplorationResult;

    QSharedPointer<ExecutableConfiguration> mNextConfiguration;
    EventHandlerDescriptorConstPtr mEntryPointEvent;

    bool mRunningFirstLoad;
    bool mRunningWithInitialValues;

    // Controls for the search procedure.

    // We can choose between entry points specified by XPath (with --concolic-button) or the built-in EP finding.
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
    QMap<QString, Symbolic::SourceIdentifierMethod> getExtraSolutionVariables(SolutionPtr solution, QStringList expected);
    void chooseNextTargetAndExplore();
    void reportStatistics();
    void triggerFieldChangeHandler(FormFieldDescriptorConstPtr field);

    QList<FormFieldDescriptorConstPtr> mFormFields;
    FormRestrictions mFormFieldRestrictions;
    FormRestrictions mFormFieldInitialRestrictions;
    QList<FormFieldDescriptorConstPtr> permuteFormFields(QList<FormFieldDescriptorConstPtr> fields, QString permutation);
    QList<int> mFormFieldPermutation;

    void updateFormFieldRestrictionsForCurrentDom();

    int mMarkerIndex;

    HandlerDependencyTracker mHandlerTracker;

    // State
    int mNumIterations;

    // Logging
    QMap<QString, InjectionValue> mPreviousInjections;
    void logInjectionValues(TraceClassificationResult classification);

private slots:
    void postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result);
    void postAllInjection();
    void postSingleInjection(FormFieldDescriptorConstPtr field);

    void slExecutionTreeUpdated(TraceNodePtr tree, QString name);

signals:
    void sigNewTraceMarker(QString label, QString index, bool isSelectRestriction, SelectRestriction selectRestriction);

};

} // namespace artemis

#endif // CONCOLICRUNTIME_H
