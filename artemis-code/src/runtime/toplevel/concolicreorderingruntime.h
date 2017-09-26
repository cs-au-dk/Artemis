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

#ifndef CONCOLICREORDERINGRUNTIME_H
#define CONCOLICREORDERINGRUNTIME_H

#include <QUrl>
#include <QMap>

#include "runtime/runtime.h"
#include "runtime/options.h"
#include "runtime/browser/artemiswebview.h"
#include "runtime/input/forms/injectionvalue.h"
#include "concolic/executiontree/classifier/traceclassifier.h"

#include "concolic/concolicanalysis.h"


namespace artemis
{

/*
 * A runtime which allows dynamic reordering of events.
 *
 * TODO: This runtime does not support form restrictions (static or dynamic).
 */

class ConcolicReorderingRuntime : public Runtime
{
    Q_OBJECT

public:
    ConcolicReorderingRuntime(QObject* parent, const Options& options, const QUrl& url);

    void run(const QUrl& url);

protected:
    QUrl mUrl;
    ArtemisWebViewPtr mWebView;
    int mNumIterations;

    // Browser part
    void preConcreteExecution();
    void clearStateForNewIteration();
    QMap<int, QPair<int, bool> > mTimers;
    void clearAsyncEvents();
    bool mRunningFirstLoad;

    // Action ordering and execution
    void setupInitialActionSequence(QSharedPointer<ExecutionResult> result);
    FormRestrictions mFormFieldRestrictions;
    void executeCurrentActionSequence();
    void printCurrentActionSequence();
    void chooseNextSequenceAndExplore();
    ConcolicAnalysis::ExplorationHandle mCurrentExplorationHandle;
    uint chooseNextActionToSearch();
    uint mPreviouslySearchedAction;
    ReachablePathsConstraintSet getReachablePathsConstraints(uint ignoreIdx);
    ReorderingConstraintInfoPtr getReorderingConstraintInfo(uint actionIdx);
    QMap<uint, InjectionValue> decodeSolvedInjectionValues(SolutionPtr solution);
    QMap<uint, InjectionValue> mSolvedInjectionValues;
    QList<uint> decodeSolvedActionOrder(SolutionPtr solution);

    InjectionValue getFieldCurrentValue(FormFieldDescriptorConstPtr field);

    struct Action {
        // TODO: Currently Action only represents form fields, but we would like to extend it to include buttons and other widgets which can be interacted with.
        uint index;
        FormFieldDescriptorConstPtr field;
        QString variable; // The name of the symbolic variable from this field (which will be the field ID).
        InjectionValue initialValue; // The default value for this field after a clean page load.
        ConcolicAnalysisPtr analysis;
        bool fullyExplored;
    };
    QMap<uint, Action> mAvailableActions; // Maps indices to actions
    QList<uint> mCurrentActionOrder; // A permutation of mAvailableActions.

    TraceClassifierPtr mTraceClassifier;

    // Logging and reporting
    QString mRunId;
    void saveConcolicTrees();

protected slots:
    // Browser part
    void postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result);
    void slTimerAdded(int timerId, int timeout, bool singleShot);
    void slTimerRemoved(int timerId);


};

} // namespace artemis
#endif // CONCOLICREORDERINGRUNTIME_H
