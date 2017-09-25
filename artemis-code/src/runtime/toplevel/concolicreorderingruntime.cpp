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

#include "concolicreorderingruntime.h"

#include "util/loggingutil.h"
#include "concolic/executiontree/tracedisplay.h"
#include "concolic/executiontree/tracedisplayoverview.h"
#include "concolic/reordering/reachablepathsconstraintgenerator.h"
#include "concolic/executiontree/classifier/formsubmissionclassifier.h"
#include "concolic/executiontree/classifier/jserrorclassifier.h"
#include "concolic/executiontree/classifier/nullclassifier.h"

namespace artemis
{

ConcolicReorderingRuntime::ConcolicReorderingRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
    , mNumIterations(0)
    , mPreviouslySearchedAction(0)
    , mRunId(QDateTime::currentDateTime().toString("yyyy-MM-dd-hh-mm-ss"))
{
    // This web view is not used and not shown, but is required to give proper geometry to the ArtemisWebPage which
    // renders the site being tested. It is required to have proper geometry in order to click correctly on elements.
    // Without this the "bare" ArtemisWebPage is laid out correctly but the document element has zero size, so any
    // click is outside its boundary and is not recognised.
    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());
    //mWebView->resize(1000,1000);
    //mWebView->show();

    // Running iterations
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(postConcreteExecution(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));

    // Managing timers
    QObject::connect(mWebkitExecutor->mWebkitListener, SIGNAL(addedTimer(int, int, bool)),
                     this, SLOT(slTimerAdded(int, int, bool)));
    QObject::connect(mWebkitExecutor->mWebkitListener, SIGNAL(removedTimer(int)),
                     this, SLOT(slTimerRemoved(int)));
    // Do not capture AJAX callbacks, force them to be fired synchronously.
    QWebExecutionListener::getListener()->doNotCaptureAjaxCallbacks();

    // Select the appropriate trace classifier.
    switch (options.concolicTraceClassifier) {
    case CLASSIFY_FORM_SUBMISSION:
        mTraceClassifier = TraceClassifierPtr(new FormSubmissionClassifier());
        break;
    case CLASSIFY_JS_ERROR:
        mTraceClassifier = TraceClassifierPtr(new JsErrorClassifier());
        break;
    case CLASSIFY_NONE:
        mTraceClassifier = TraceClassifierPtr(new NullClassifier());
        break;
    default:
        Log::fatal("Unsupported classification method.");
        exit(1);
    }
}

void ConcolicReorderingRuntime::run(const QUrl &url)
{
    mUrl = url;

    // There is nothing else to prepare... Start the first iteration.
    Log::info(QString("Beginning analysis of %1").arg(url.toString()).toStdString());
    mRunningFirstLoad = true;
    preConcreteExecution();
}


void ConcolicReorderingRuntime::preConcreteExecution()
{
    // Begins a new iteration and initiates the new page load.

    // Check if we have reached the iteration limit.
    if (mOptions.iterationLimit > 0 && mOptions.iterationLimit <= mNumIterations) {
        Log::info("Iteration limit reached");
        mWebkitExecutor->detach();
        done();
        return;
    }
    mNumIterations++;

    Log::debug("\n============= New-Iteration =============");
    Log::info(QString("Iteration %1:").arg(mNumIterations).toStdString());
    clearStateForNewIteration();

    // N.B. Unlike the main concolic mode (concolicruntime.cpp), we do not do the input actions as part of the configuration.
    // This mode works more like server mode: we let WebkitExecutor do the page load and nothing more.
    // Then this runtime takes over and manages the concolic trace recording and form injections directly.
    ExecutableConfigurationPtr noInput = ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), mUrl));
    mWebkitExecutor->executeSequence(noInput, MODE_CONCOLIC_NO_TRACE); // Calls postConcreteExecution as a callback
}

void ConcolicReorderingRuntime::clearStateForNewIteration()
{
    // Clear all cookies.
    // In this mode the cookie jar will always be of type ResettableCookieJar (see options.saveCookiesForSession in artemis.cpp).
    QNetworkCookieJar* cookieJar = mWebkitExecutor->getCookieJar();
    ResettableCookieJar* resettableCookieJar = dynamic_cast<ResettableCookieJar*>(cookieJar);
    if (resettableCookieJar) {
        resettableCookieJar->reset();
    }
}


void ConcolicReorderingRuntime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // Called once we have finished the page load. Now it is time to begin the trace execution.

    // Process any async events which already exist immediately after the page load.
    clearAsyncEvents();

    // If this is the first run, detect and set up the available actions.
    if (mRunningFirstLoad) {
        setupInitialActionSequence(result);
        mRunningFirstLoad = false;
    }

    // Execute the current action sequence
    executeCurrentActionSequence();

    // Choose the new values and actions to test
    chooseNextSequenceAndExplore();

}



void ConcolicReorderingRuntime::slTimerAdded(int timerId, int timeout, bool singleShot)
{
    assert(!mTimers.contains(timerId));
    mTimers.insert(timerId, QPair<int, bool>(timeout, singleShot));
}

void ConcolicReorderingRuntime::slTimerRemoved(int timerId)
{
    // N.B. clearAsyncEvents removes IDs manually, so we do no necessarily expect timerId to still be in mTimers.
    mTimers.remove(timerId);
}

// TODO: This is duplicated from analysisserverruntime.cpp
void ConcolicReorderingRuntime::clearAsyncEvents()
{
    // AJAX events are handled synchronously (see call to doNotCaptureAjaxCallbacks in the constructor) so they are ignored here.

    // Fire all timers up to depth 4. i.e. 4 levels of nested timers, or 4 rounds of interval timers.
    for (int i = 0; i < 4 && !mTimers.isEmpty(); i++) {
        QList<int> currentRoundTimers = mTimers.keys();
        qSort(currentRoundTimers); // Take timers in ID order.
        Log::debug(QString("  CAE: Firing timers in round %1 (%2 timers)").arg(i).arg(currentRoundTimers.length()).toStdString());
        foreach(int timerId, currentRoundTimers) {
            if (!mTimers.contains(timerId)) {
                continue; // This timer must have been removed by an earlier timer in this round.
            }
            bool singleShot = mTimers[timerId].second;

            Log::debug(QString("  CAE: Fire timer %1").arg(timerId).toStdString());
            // N.B. This may add new timers to mTimers, which we will pick up in the next round.
            mWebkitExecutor->mWebkitListener->timerFire(timerId);
            Statistics::statistics()->accumulate("ConcolicReordering::ClearAsyncEvents::TimersTriggered", 1);
            if (singleShot) {
                mTimers.remove(timerId); // This will also get removed by timerCancel, but it may not be immediate.
                mWebkitExecutor->mWebkitListener->timerCancel(timerId);
                Statistics::statistics()->accumulate("ConcolicReordering::ClearAsyncEvents::TimersTriggered", 1);
            }
        }
    }

    // Cancel any outstanding timers.
    foreach (int timerId, mTimers.keys()) {
        Log::debug(QString("  CAE: Cancelling timer %1").arg(timerId).toStdString());
        mTimers.remove(timerId); // This will also get removed by timerCancel, but it may not be immediate.
        mWebkitExecutor->mWebkitListener->timerCancel(timerId);
        Statistics::statistics()->accumulate("ConcolicReordering::ClearAsyncEvents::TimersCancelled", 1);
    }

    // Now all async events are executed or removed, so there should be no background execution in the browser.
}



void ConcolicReorderingRuntime::setupInitialActionSequence(QSharedPointer<ExecutionResult> result)
{
    // Populate mAvailableActions and set the default ordering in mCurrentActionOrder.
    // TODO: mAvailaleActions should probably be given as input, or at least be configurable. For now (for testing) we can just take all fields.
    // For the first iteration, the actions are taken in index order (i.e. DOM order).

    QList<FormFieldDescriptorConstPtr> fieldsOnPage = result->getFormFields();
    mFormFieldRestrictions = FormFieldRestrictedValues::getRestrictions(fieldsOnPage, mWebkitExecutor->getPage());
    uint fieldIdx = 0;
    foreach (FormFieldDescriptorConstPtr field, fieldsOnPage) {
        Action action;
        action.index = ++fieldIdx;
        action.field = field;
        action.variable = field->getDomElement()->getId();
        action.initialValue = getFieldCurrentValue(action.field);
        action.analysis = ConcolicAnalysisPtr(new ConcolicAnalysis(mOptions, ConcolicAnalysis::QUIET));
        action.fullyExplored = false;

        action.analysis->setFormRestrictions(mFormFieldRestrictions);

        mAvailableActions[action.index] = action;
        mCurrentActionOrder.append(action.index);

        // Set all fields to be symbolic all the time.
        // In the concolic mode this is only done during the injection, as we have a fixed ordering.
        // In the server mode, everything is symbolic, and it causes some invalid suggestions.
        // Here, it will be safe because we can explicitly model the relationships between events and the orderings.
        action.field->getDomElement()->getElement(mWebkitExecutor->getPage()).evaluateJavaScript("this.symbolictrigger == \"\";", QUrl(), true);
        action.field->getDomElement()->getElement(mWebkitExecutor->getPage()).evaluateJavaScript("this.options.symbolictrigger == \"\";", QUrl(), true);
    }
}

void ConcolicReorderingRuntime::executeCurrentActionSequence()
{
    printCurrentActionSequence();
    Log::debug("Executing...");

    foreach (uint actionIdx, mCurrentActionOrder) {
        Action action = mAvailableActions[actionIdx];

        // Look up the value to inject in the solver's result.
        // If it does not exist, or this is the first iteration, then use the current/default value.
        // TODO: get the solved value!
        InjectionValue injection = getFieldCurrentValue(action.field);

        // Begin trace recording for this action
        mWebkitExecutor->getTraceBuilder()->beginRecording();

        // Fill the field, simulating a user action.
        Log::debug(QString("Executing action %1 (field %2, value %3, JS user simulation)").arg(action.index).arg(action.variable).arg(injection.toString()).toStdString());
        bool couldInject = FormFieldInjector::injectWithEventSimulation(action.field->getDomElement()->getElement(mWebkitExecutor->getPage()), injection, false);
        if (!couldInject) {
            Log::error("Error: failed to inject.");
        }
        clearAsyncEvents();

        // End trace recording
        mWebkitExecutor->getTraceBuilder()->endRecording();
        TraceNodePtr trace = mWebkitExecutor->getTraceBuilder()->trace();
        mTraceClassifier->classify(trace);

        // TODO: Save the exploration target from a solver solution and use it here so the tree can match up targets and attempts.
        action.analysis->addTrace(trace, ConcolicAnalysis::NO_EXPLORATION_TARGET);
    }

    // TODO: Should there be a way to set one action as "always last"?

    saveConcolicTrees();
}

void ConcolicReorderingRuntime::printCurrentActionSequence()
{
    Log::debug("Current action sequence:");

    uint pos = 0;
    foreach (uint actionIdx, mCurrentActionOrder) {
        Action action = mAvailableActions[actionIdx];
        Log::debug(QString("  #%1: Action %2 (%3)").arg(++pos).arg(action.index).arg(action.variable).toStdString());
    }
}

InjectionValue ConcolicReorderingRuntime::getFieldCurrentValue(FormFieldDescriptorConstPtr field)
{
    // Get the defualt/current value for this field from the DOM and return it as an InjectionValue.
    switch (field->getType()) {
    case FormFieldTypes::TEXT:
        return InjectionValue(field->getDomElement()->getElement(mWebkitExecutor->getPage()).attribute("value"));
    case FormFieldTypes::FIXED_INPUT:
        // TODO: For some reason, calling .attribute("value") returns an empty string, even after a JS injection to set that property (similarly to FormFieldRestrictedValues::getRestrictions().
        // For some reason we need this little JS injection to get the value.
        return InjectionValue(field->getDomElement()->getElement(mWebkitExecutor->getPage()).evaluateJavaScript("this.value", QUrl(), true).toString());
    case FormFieldTypes::BOOLEAN:
        return InjectionValue(field->getDomElement()->getElement(mWebkitExecutor->getPage()).hasAttribute("checked"));
    case FormFieldTypes::NO_INPUT:
    default:
        Log::fatal("Trying to get the value for a form field which is not an input!");
        Log::fatal(field->getDomElement()->getId().toStdString());
        exit(1);
    }
}

void ConcolicReorderingRuntime::chooseNextSequenceAndExplore()
{
    // Choose the action to explore next.
    uint nextActionIdx = chooseNextActionToSearch();
    if (nextActionIdx == 0) {
        // No action could be found to explore. N.B. 0 is not a valid index; they start at 1.
        Log::info("ConcolicReorderingRuntime: There were no actions left to explore. Done.");
        saveConcolicTrees();
        mWebkitExecutor->detach();
        done();
    }

    Action nextAction = mAvailableActions[nextActionIdx];
    Log::debug("ConcolicReorderingRuntime: exploring action " + std::to_string(nextActionIdx) + " (" + nextAction.variable.toStdString() + ")");

    // Collate the reachable-paths constraints for the other actions.
    ReachablePathsConstraintSet reachablePaths = getReachablePathsConstraints(nextActionIdx);

    // Select a target branch from the chosen action's concolic tree.
    nextAction.analysis->setReachablePathsConstraints(reachablePaths);
    nextAction.analysis->setReorderingInfo(getReorderingConstraintInfo(nextAction.index));
    ConcolicAnalysis::ExplorationResult result = nextAction.analysis->nextExploration();
    if (result.newExploration) {
        // Succesfully solved a PC in this action.
        Log::debug("ConcolicReorderingRuntime: exploration succeeded.");

        // Decode the variables to be injected.
        decodeSolvedInjectionValues();

        // Decode the ordering to be used.
        mCurrentActionOrder = decodeSolvedActionOrder(result.solution);
        Log::debug("Solved action sequence:");
        printCurrentActionSequence();

        // Prepare the next execution.
        // TODO

    } else {
        // Couldn't explore in this action. Try another one.
        Log::debug("ConcolicReorderingRuntime: exploration faield.");
        nextAction.fullyExplored = true; // Do not return to this action.
        chooseNextSequenceAndExplore();
    }

    // TODO
    Log::fatal("This analysis is not yet implemented. Quitting.");
    saveConcolicTrees();
    done();
}

uint ConcolicReorderingRuntime::chooseNextActionToSearch()
{
    // Check which actions are not fully explored.
    QList<uint> actionsToExplore;
    foreach (Action action, mAvailableActions) {
        if (!action.fullyExplored) {
            actionsToExplore.append(action.index);
        }
    }
    if (actionsToExplore.isEmpty()) {
        Log::debug("ConcolicReorderingRuntime::chooseNextActionToSearch: Did not find any action to search.");
        return 0; // N.B. 0 is not a valid index; they start at 1.
    }

    // Use round-robin to select an action to search.
    qSort(actionsToExplore);
    if (mPreviouslySearchedAction == 0) {
        mPreviouslySearchedAction = actionsToExplore[0];
        return actionsToExplore[0];
    }
    foreach (uint actionIdx, actionsToExplore) {
        if (actionIdx > mPreviouslySearchedAction) {
            mPreviouslySearchedAction = actionIdx;
            return actionIdx;
        }
    }
    // Otherwise we have wrapped around to the start again.
    mPreviouslySearchedAction = actionsToExplore[0];
    return actionsToExplore[0];
}

ReachablePathsConstraintSet ConcolicReorderingRuntime::getReachablePathsConstraints(uint ignoreIdx)
{
    // Collate the reachable-paths constraints for the actions other than ignoreIdx.
    // TODO: Ideally this would be maintained and updated dynamically as-needed, and not re-built on every iteration.

    ReachablePathsConstraintSet constraintSet;
    foreach (uint actionIdx, mAvailableActions.keys()) {
        if (actionIdx != ignoreIdx) {
            Action action = mAvailableActions[actionIdx];
            NamedReachablePathsConstraint constraint;
            constraint.first = QPair<QString, uint>(QString("Action %1 (%2)").arg(actionIdx).arg(action.variable), action.index);
            constraint.second = ReachablePathsConstraintGenerator::generateConstraint(action.analysis->getExecutionTree());
            constraintSet.insert(constraint);
        }
    }

    return constraintSet;
}

ReorderingConstraintInfoPtr ConcolicReorderingRuntime::getReorderingConstraintInfo(uint actionIdx)
{
    // Create the concolic renaming/reordering info for this concolic analysis.
    QMap<uint, QPair<QString, InjectionValue>> actionVariables;
    QMap<uint, QPair<QString, InjectionValue>> actionIndexVariables;
    InjectionValue defaultIndex;
    foreach (Action action, mAvailableActions) {
        switch (action.field->getType()) {
        case TEXT:
            actionVariables.insert(action.index, QPair<QString, InjectionValue>("SYM_IN_" + action.variable, action.initialValue));
            break;
        case FIXED_INPUT:
            // Use the default value to look up the default index.
            defaultIndex = InjectionValue(-1);
            foreach (SelectRestriction sr, mFormFieldRestrictions.first) {
                //Log::debug("CHECKING " + sr.variable.toStdString() + " == " + action.variable.toStdString());
                if (sr.variable == action.variable) {
                    assert(action.initialValue.getType() == QVariant::String);
                    //Log::debug("CHECKING '" + action.initialValue.getString().toStdString() + "'");
                    if (sr.values.contains(action.initialValue.getString())) {
                        defaultIndex = InjectionValue(sr.values.indexOf(action.initialValue.getString()));
                    }
                }
            }

            actionVariables.insert(action.index, QPair<QString, InjectionValue>("SYM_IN_" + action.variable, action.initialValue));
            actionIndexVariables.insert(action.index, QPair<QString, InjectionValue>("SYM_IN_INT_" + action.variable, defaultIndex));
            // N.B. The integer variable for the selectedIndex is handled indirectly via the form restrictions.
            break;
        case BOOLEAN:
            actionVariables.insert(action.index, QPair<QString, InjectionValue>("SYM_IN_BOOL" + action.variable, action.initialValue));
            break;
        case NO_INPUT:
        default:
            Log::fatal("Unexpected variable type encountered in ConcolicReorderingRuntime::getReorderingConstraintInfo.");
            exit(1);
        }
    }

    ReorderingConstraintInfoPtr reorderingInfo = ReorderingConstraintInfoPtr(new ReorderingConstraintInfo(actionVariables, actionIndexVariables, actionIdx));
    return reorderingInfo;
}

void ConcolicReorderingRuntime::decodeSolvedInjectionValues()
{
    // TODO
}

QList<uint> ConcolicReorderingRuntime::decodeSolvedActionOrder(SolutionPtr solution)
{
    // Extract the next ordering from the SYM_ORDERING_* variables in the solution.
    // N.B. The SYM_ORDERING_* naming scheme must match with SMTConstraintWriter::emitLinearOrderingConstraints()

    // For each action i, extract SYM_ORDERING_i and record it in positionsToActions
    QMap<uint, uint> positionsToActions;
    foreach (uint actionIdx, mAvailableActions.keys()) {
        QString orderingVar = QString("SYM_ORDERING_%1").arg(actionIdx);
        Symbolvalue value = solution->findSymbol(orderingVar);
        if (!value.found) {
            Log::fatal(QString("ConcolicReorderingRuntime::decodeSolvedActionOrder: Could not find %1").arg(orderingVar).toStdString());
            exit(1);
        }
        if (value.kind != Symbolic::INT) {
            Log::fatal(QString("ConcolicReorderingRuntime::decodeSolvedActionOrder: Found the wrong type for %1").arg(orderingVar).toStdString());
            exit(1);
        }
        uint actionPosition = (uint)value.u.integer;
        if (positionsToActions.contains(actionPosition)) {
            Log::fatal(QString("ConcolicReorderingRuntime::decodeSolvedActionOrder: Found duplicate actions for position %1").arg(actionPosition).toStdString());
            exit(1);
        }
        positionsToActions.insert(actionPosition, actionIdx);
    }

    // Flatten positionsToActions into a list.
    // N.B. we assume the positions must be exactly the set 1..N
    uint N = (uint)mAvailableActions.size();
    QList<uint> result;
    for (uint pos=1; pos<=N; pos++) {
        if (!positionsToActions.contains(pos)) {
            Log::fatal(QString("ConcolicReorderingRuntime::decodeSolvedActionOrder: Found no action for position %1").arg(pos).toStdString());
            exit(1);
        }
        result.append(positionsToActions[pos]);
    }

    return result;
}



void ConcolicReorderingRuntime::saveConcolicTrees()
{
    if(mOptions.concolicTreeOutput == TREE_NONE){
        return;
    }

    TraceDisplay display(mOptions.outputCoverage != NONE);
    TraceDisplayOverview display_min(mOptions.outputCoverage != NONE);

    foreach (uint actionIdx, mAvailableActions.keys()) {
        Action action = mAvailableActions[actionIdx];

        QString name = QString("tree-%1_%2_A%3.gv").arg(mRunId).arg(mNumIterations).arg(action.index);
        QString name_min = QString("tree-%1_min_%2_A%3.gv").arg(mRunId).arg(mNumIterations).arg(action.index);
        QString title = QString("URL: %1\\nRun: %2\\nAction %3 (%4)").arg(mUrl.toString()).arg(mRunId).arg(action.index).arg(action.variable);

        Log::debug(QString("CONCOLIC-INFO: Writing tree to file %1").arg(name).toStdString());
        display.writeGraphFile(action.analysis->getExecutionTree(), name, false, title);
        if (mOptions.concolicTreeOutputOverview) {
            display_min.writeGraphFile(action.analysis->getExecutionTree(), name_min, false, title);
        }
    }

    // TODO: Do not overwrite old files unless we are in mode TREE_FINAL.
}





} // namespace artemis
