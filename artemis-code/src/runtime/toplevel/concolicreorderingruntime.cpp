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
#include "concolic/tracestatistics.h"
#include "runtime/input/clicksimulator.h"

namespace artemis
{

ConcolicReorderingRuntime::ConcolicReorderingRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
    , mNumIterations(0)
    , mCurrentExplorationHandle(ConcolicAnalysis::NO_EXPLORATION_TARGET)
    , mPreviouslySearchedAction(0)
    , mFoundFullyTerminatingTrace(false)
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

    enableAsyncEventCapture();

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

    // If we are using a submit button, then set this up.
    if (!mOptions.concolicEntryPoint.isNull()) {
        mSubmitButtonSelector = mOptions.concolicEntryPoint;
        mSubmitButtonAnalysis = ConcolicAnalysisPtr(new ConcolicAnalysis(mOptions, ConcolicAnalysis::QUIET));
        mSubmitButtonFullyExplored = false;
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
    makeAllFieldsSymbolic();
    executeCurrentActionSequence();

    // Choose the new values and actions to test
    chooseNextSequenceAndExplore();

}





void ConcolicReorderingRuntime::setupInitialActionSequence(QSharedPointer<ExecutionResult> result)
{
    // Populate mAvailableActions and set the default ordering in mCurrentActionOrder.
    // For the first iteration, the actions are taken in index order (i.e. DOM order).

    // Filter the list of fields according to concolic-form-area.
    // TODO: Duplicated from code in concolicruntime.cpp
    QList<FormFieldDescriptorConstPtr> fieldsOnPage;
    if (!mOptions.eventFilterArea.isNull()) {
        // Look up the form area subtree.
        QWebElement formAreaRoot = mWebkitExecutor->getPage()->getSingleElementByXPath(mOptions.eventFilterArea);
        if (formAreaRoot.isNull()) {
            Log::error("Could not identify a single root element for the concolic form area.");
            exit(1);
        }
        QList<QWebElement> formAreaElements = formAreaRoot.findAll("*").toList();
        foreach (FormFieldDescriptorConstPtr field, result->getFormFields()) {
            if (formAreaElements.contains(field->getDomElement()->getElement(mWebkitExecutor->getPage()))) {
                fieldsOnPage.append(field);
            }
        }
    } else {
        fieldsOnPage = result->getFormFields();
        // TODO: Also have an "auto" mode which chooses the first form element enclosing the chosen submit button.
    }

    mFormFieldRestrictions = FormFieldRestrictedValues::getRestrictions(fieldsOnPage, mWebkitExecutor->getPage());
    uint fieldIdx = 0;
    QStringList orderingSummary;
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

        orderingSummary.append(QString::number(fieldIdx));
    }
    if (!mSubmitButtonSelector.isNull()) {
        orderingSummary.append("Btn");
    }
    mOrderingLog.append(orderingSummary.join(", "));

    // Give the submit button the next/final index.
    mSubmitButtonIndex = fieldIdx + 1;
}

void ConcolicReorderingRuntime::makeAllFieldsSymbolic()
{
    // Set all fields to be symbolic all the time.
    // In the concolic mode this is only done during the injection, as we have a fixed ordering.
    // In the server mode, everything is symbolic, and it causes some invalid suggestions.
    // Here, it will be safe because we can explicitly model the relationships between events and the orderings.
    foreach (Action action, mAvailableActions) {
        action.field->getDomElement()->getElement(mWebkitExecutor->getPage()).evaluateJavaScript("this.symbolictrigger == \"\";", QUrl(), true);
        action.field->getDomElement()->getElement(mWebkitExecutor->getPage()).evaluateJavaScript("this.options.symbolictrigger == \"\";", QUrl(), true);
    }
}

void ConcolicReorderingRuntime::executeCurrentActionSequence()
{
    Log::debug("Current action sequence:");
    printCurrentActionSequence();
    Log::debug("Executing...");

    bool allActionsTerminate = true;
    foreach (uint actionIdx, mCurrentActionOrder) {
        Action action = mAvailableActions[actionIdx];

        // Look up the value to inject in the solver's result.
        // If it does not exist, or this is the first iteration, then use the current/default value.
        // TODO: get the solved value!
        InjectionValue injection;
        if (mSolvedInjectionValues.contains(actionIdx)) {
            injection = mSolvedInjectionValues[actionIdx];
        } else {
            injection = getFieldCurrentValue(action.field);
        }

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

        TraceClassificationResult classification = mTraceClassifier->classify(trace);
        if (classification == FAILURE) {
            allActionsTerminate = false;
        }

        if (actionIdx == mPreviouslySearchedAction) {
            action.analysis->addTrace(trace, mCurrentExplorationHandle);
        } else {
            action.analysis->addTrace(trace, ConcolicAnalysis::NO_EXPLORATION_TARGET);
        }
    }

    // Also fire and record the submit button action.
    if (!mSubmitButtonSelector.isNull()) {
        assert(!mSubmitButtonAnalysis.isNull());
        Log::debug("Executing submit button click");

        // Look up the submit button element.
        QWebElement target = mWebkitExecutor->getPage()->getSingleElementByXPath(mSubmitButtonSelector);
        if (target.isNull()) {
            Log::fatal("ConcolicReorderingRuntime::executeCurrentActionSequence: Click target could not be found. The XPath either did not match or matched multiple elements.");
            exit(1);
        }

        mWebkitExecutor->getTraceBuilder()->beginRecording();

        ClickSimulator::clickByUserEventSimulation(target);
        clearAsyncEvents();

        mWebkitExecutor->getTraceBuilder()->endRecording();
        TraceNodePtr trace = mWebkitExecutor->getTraceBuilder()->trace();

        TraceClassificationResult classification = mTraceClassifier->classify(trace);
        if (classification == FAILURE) {
            allActionsTerminate = false;
        }

        if (mPreviouslySearchedAction == mSubmitButtonIndex) {
            mSubmitButtonAnalysis->addTrace(trace, mCurrentExplorationHandle);
        } else {
            mSubmitButtonAnalysis->addTrace(trace, ConcolicAnalysis::NO_EXPLORATION_TARGET);
        }
    }

    if (allActionsTerminate) {
        Statistics::statistics()->accumulate("Concolic::Reordering::FullyTerminatingTraces", 1);

        if (!mFoundFullyTerminatingTrace) {
            mFoundFullyTerminatingTrace = true;
            Statistics::statistics()->set("Concolic::Reordering::FirstFullyTerminatingTraceIteration", mNumIterations);
            Statistics::statistics()->set("Concolic::Reordering::FirstFullyTerminatingTraceTimeMS", std::to_string(mRunningTime.elapsed()));
            // N.B. This is not as meaningful in this mode as in others. It is perfectly possible to find terminating traces in all trees but to never have explored them all simultaneously.
        }
    }

    saveConcolicTrees();
}

void ConcolicReorderingRuntime::printCurrentActionSequence()
{
    uint pos = 0;
    foreach (uint actionIdx, mCurrentActionOrder) {
        Action action = mAvailableActions[actionIdx];
        QString injection;
        if (mSolvedInjectionValues.contains(actionIdx)) {
            injection = mSolvedInjectionValues[actionIdx].getType() == QVariant::String ? "\""+mSolvedInjectionValues[actionIdx].toString()+"\"" : mSolvedInjectionValues[actionIdx].toString();
        } else {
            injection = "[unchanged] (initially " + (action.initialValue.getType() == QVariant::String ? "\""+action.initialValue.toString()+"\"" : action.initialValue.toString()) + ")";
        }
        Log::debug(QString("  #%1: Action %2 (%3). Injecting %4").arg(++pos).arg(action.index).arg(action.variable).arg(injection).toStdString());
    }
    if (!mSubmitButtonSelector.isNull()) {
        Log::debug(QString("  #%1: Submit button click").arg(mSubmitButtonIndex).toStdString());
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
        mWebkitExecutor->detach();
        done();
    }

    ConcolicAnalysisPtr analysis;
    if (!mSubmitButtonAnalysis.isNull() && nextActionIdx == mSubmitButtonIndex) {
        Log::debug("ConcolicReorderingRuntime: Exploring submit button");
        analysis = mSubmitButtonAnalysis;
    } else {
        Action nextAction = mAvailableActions[nextActionIdx];
        Log::debug("ConcolicReorderingRuntime: Exploring action " + std::to_string(nextActionIdx) + " (" + nextAction.variable.toStdString() + ")");
        analysis = nextAction.analysis;
    }

    // Collate the reachable-paths constraints for the other actions.
    ReachablePathsConstraintSet reachablePaths = getReachablePathsConstraints(nextActionIdx);

    // Select a target branch from the chosen action's concolic tree.
    analysis->setReachablePathsConstraints(reachablePaths);
    analysis->setReorderingInfo(getReorderingConstraintInfo(nextActionIdx));
    ConcolicAnalysis::ExplorationResult result = analysis->nextExploration();
    if (result.newExploration) {
        // Succesfully solved a PC in this action.
        Log::debug("ConcolicReorderingRuntime: exploration succeeded.");

        // Decode the variables to be injected.
        mSolvedInjectionValues = decodeSolvedInjectionValues(result.solution);

        // Decode the ordering to be used.
        mCurrentActionOrder = decodeSolvedActionOrder(result.solution);
        Log::debug("Solved action sequence:");
        printCurrentActionSequence();

        QStringList orderingSummary;
        foreach (uint x, mCurrentActionOrder) {
            orderingSummary.append(QString::number(x));
        }
        if (!mSubmitButtonSelector.isNull()) {
            orderingSummary.append("Btn");
        }
        mOrderingLog.append(orderingSummary.join(", "));

        // Prepare the next execution.
        mCurrentExplorationHandle = result.target;
        preConcreteExecution();

    } else {
        // Couldn't explore in this action. Try another one.
        Log::debug("ConcolicReorderingRuntime: exploration faield.");
        // Do not return to this action.
        if (nextActionIdx == mSubmitButtonIndex) {
            mSubmitButtonFullyExplored = true;
        } else {
            mAvailableActions[nextActionIdx].fullyExplored = true;
        }
        chooseNextSequenceAndExplore();
    }
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
    if (!mSubmitButtonSelector.isNull() && !mSubmitButtonFullyExplored) {
        actionsToExplore.append(mSubmitButtonIndex);
    }
    if (actionsToExplore.isEmpty()) {
        Log::debug("ConcolicReorderingRuntime::chooseNextActionToSearch: Did not find any action to search.");
        return 0; // N.B. 0 is not a valid index; they start at 1.
    }

    // Use round-robin to select an action to search.
    qSort(actionsToExplore);
    // On the first run, choose the first action.
    if (mPreviouslySearchedAction == 0) {
        mPreviouslySearchedAction = actionsToExplore[0];
        return actionsToExplore[0];
    }
    // If we are in the middle of the action sequence, choose the next action.
    foreach (uint actionIdx, actionsToExplore) {
        if (actionIdx > mPreviouslySearchedAction) {
            mPreviouslySearchedAction = actionIdx;
            return actionIdx;
        }
    }
    // If we overflow the actions list, the submit button is next.
    // N.B. This check works because we guarantee the submit button has a higher index than all the other actions.
    if (actionsToExplore.contains(mSubmitButtonIndex) && mSubmitButtonIndex > mPreviouslySearchedAction) {
        mPreviouslySearchedAction = mSubmitButtonIndex;
        return mSubmitButtonIndex;
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

    // Also emit the constraint for the submit button handler.
    if (!mSubmitButtonSelector.isNull() && mSubmitButtonIndex != ignoreIdx) {
        NamedReachablePathsConstraint constraint;
        constraint.first = QPair<QString, uint>("submit button", mSubmitButtonIndex);
        constraint.second = ReachablePathsConstraintGenerator::generateConstraint(mSubmitButtonAnalysis->getExecutionTree());
        constraintSet.insert(constraint);
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

    ReorderingConstraintInfoPtr reorderingInfo = ReorderingConstraintInfoPtr(new ReorderingConstraintInfo(actionVariables, actionIndexVariables, actionIdx, (mSubmitButtonSelector.isNull() ? 0 : mSubmitButtonIndex)));
    return reorderingInfo;

    // N.B. We do not have to account for the submit button action; it is always last, so we do not handle it in the solver.
}

QMap<uint, InjectionValue> ConcolicReorderingRuntime::decodeSolvedInjectionValues(SolutionPtr solution)
{
    // mAvailableActions gives the variables we are looking for.
    // Those which are not in the Solution object will get their default values.

    QMap<uint, InjectionValue> result;
    foreach (Action action, mAvailableActions) {
        QString symbolName;
        switch (action.field->getType()) {
        case TEXT:
        case FIXED_INPUT:
            symbolName = "SYM_IN_" + action.variable;
            break;
        case BOOLEAN:
            symbolName = "SYM_IN_BOOL_" + action.variable;
            break;
        case NO_INPUT:
        default:
            Log::fatal("Unexpected field type encountered in ConcolicReorderingRuntime::decodeSolvedInjectionValues");
            exit(1);
        }

        Symbolvalue value = solution->findSymbol(symbolName);
        if (value.found) {
            switch (value.kind) {
            case Symbolic::BOOL:
                result.insert(action.index, InjectionValue(value.u.boolean));
                break;
            case Symbolic::STRING:
                result.insert(action.index, InjectionValue(QString::fromStdString(value.string)));
                break;
            case Symbolic::INT:
            default:
                Log::fatal("Unexpected solved value type encountered in ConcolicReorderingRuntime::decodeSolvedInjectionValues.");
            }
        }
    }
    return result;
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
    QSet<QString> treeFileNames;

    TraceDisplay display(mOptions.outputCoverage != NONE);
    TraceDisplayOverview display_min(mOptions.outputCoverage != NONE);

    foreach (uint actionIdx, mAvailableActions.keys()) {
        Action action = mAvailableActions[actionIdx];

        QString name = QString("tree-%1_%2_A%3.gv").arg(mRunId).arg(mNumIterations).arg(action.index);
        QString name_min = QString("tree-%1_min_%2_A%3.gv").arg(mRunId).arg(mNumIterations).arg(action.index);
        QString title = QString("URL: %1\\nRun: %2\\nAction %3 (%4)").arg(mUrl.toString()).arg(mRunId).arg(action.index).arg(action.variable);

        Log::debug(QString("CONCOLIC-INFO: Writing tree to file %1").arg(name).toStdString());
        display.writeGraphFile(action.analysis->getExecutionTree(), name, false, title);
        treeFileNames.insert(name);
        if (mOptions.concolicTreeOutputOverview) {
            display_min.writeGraphFile(action.analysis->getExecutionTree(), name_min, false, title);
            treeFileNames.insert(name_min);
        }
    }

    // Also save the submit button tree.
    if (!mSubmitButtonAnalysis.isNull()) {
        QString name = QString("tree-%1_%2_Btn.gv").arg(mRunId).arg(mNumIterations);
        QString name_min = QString("tree-%1_min_%2_Btn.gv").arg(mRunId).arg(mNumIterations);
        QString title = QString("URL: %1\\nRun: %2\\nSubmit button click").arg(mUrl.toString()).arg(mRunId);

        Log::debug(QString("CONCOLIC-INFO: Writing tree to file %1").arg(name).toStdString());
        display.writeGraphFile(mSubmitButtonAnalysis->getExecutionTree(), name, false, title);
        treeFileNames.insert(name);
        if (mOptions.concolicTreeOutputOverview) {
            display_min.writeGraphFile(mSubmitButtonAnalysis->getExecutionTree(), name_min, false, title);
            treeFileNames.insert(name_min);
        }
    }

    // If we are in TREE_FINAL mode, then remove the old trees.
    if (mOptions.concolicTreeOutput == TREE_FINAL) {
        mOldTreeFiles.subtract(treeFileNames); // Do not remove any just-written trees, in case this method is called twice with the same settings.
        foreach (QString name, mOldTreeFiles) {
            QFile::remove(name);
        }
        mOldTreeFiles = treeFileNames;
    }
}


// TODO: This function is mostly duplicated in concolicruntime.cpp and concolicstandaloneruntime.cpp.
void ConcolicReorderingRuntime::reportStatistics()
{
    Statistics::statistics()->accumulate("Concolic::Iterations", mNumIterations);

    foreach (Action action, mAvailableActions) {
        reportStatisticsForTree(action.analysis->getExecutionTree());
    }

    // Also include the button click action
    if (!mSubmitButtonAnalysis.isNull()) {
        reportStatisticsForTree(mSubmitButtonAnalysis->getExecutionTree());
    }

    // Also add some statistics about the new reordering algorithm.
    Statistics::statistics()->accumulate("Concolic::Reordering::TotalActionsExplored", mAvailableActions.size());
    foreach (Action action, mAvailableActions) {
        if (action.fullyExplored) {
            Statistics::statistics()->accumulate("Concolic::Reordering::TotalActionsFullyExplored", 1);
        }
    }
    Statistics::statistics()->accumulate("Concolic::Reordering::UniqueOrderingsTested", mOrderingLog.toSet().size());

    if (!mSubmitButtonSelector.isNull()) {
        Statistics::statistics()->accumulate("Concolic::Reordering::TotalActionsExplored", 1);
        if (mSubmitButtonFullyExplored) {
            Statistics::statistics()->accumulate("Concolic::Reordering::TotalActionsFullyExplored", 1);
        }
    }
}

void ConcolicReorderingRuntime::reportStatisticsForTree(TraceNodePtr tree)
{
    TraceStatistics stats;
    stats.processTrace(tree);

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::ConcreteBranchesTotal", stats.mNumConcreteBranches);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::ConcreteBranchesFullyExplored", stats.mNumConcreteBranchesFullyExplored);

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::SymbolicBranchesTotal", stats.mNumSymBranches);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::SymbolicBranchesFullyExplored", stats.mNumSymBranchesFullyExplored);

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::Alerts", stats.mNumAlerts);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::ConsoleMessages", stats.mNumConsoleMessages);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::PageLoads", stats.mNumPageLoads);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::InterestingDomModifications", stats.mNumInterestingDomModifications);

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::EndSuccess", stats.mNumEndSuccess);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::EndFailure", stats.mNumEndFailure);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::EndUnknown", stats.mNumEndUnknown);

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::Unexplored", stats.mNumUnexplored);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::UnexploredSymbolicChild", stats.mNumUnexploredSymbolicChild);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::Unsat", stats.mNumUnexploredUnsat);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::Missed", stats.mNumUnexploredMissed);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::CouldNotSolve", stats.mNumUnexploredUnsolvable);

    //Statistics::statistics()->accumulate("Concolic::EventSequence::HandlersTriggered", mFormFields.size());
    Statistics::statistics()->accumulate("Concolic::EventSequence::SymbolicBranchesTotal", stats.mNumEventSequenceSymBranches);
    Statistics::statistics()->accumulate("Concolic::EventSequence::SymbolicBranchesFullyExplored", stats.mNumEventSequenceSymBranchesFullyExplored);
}

void ConcolicReorderingRuntime::done()
{
    saveConcolicTrees();
    reportStatistics();

    Log::debug("Orderings explored:");
    foreach (QString order, mOrderingLog) {
        Log::debug("    " + order.toStdString());
    }

    Runtime::done();
}




} // namespace artemis
