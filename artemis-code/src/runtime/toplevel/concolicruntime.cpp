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

#include <fstream>
#include <assert.h>

#include "util/loggingutil.h"
#include "concolic/executiontree/tracenodes.h"
#include "concolic/traceeventdetectors.h"
#include "concolic/solver/cvc4solver.h"
#include "statistics/statsstorage.h"

#include "concolic/search/searchdfs.h"
#include "concolic/search/randomaccesssearch.h"
#include "concolic/search/avoidunsatselector.h"
#include "concolic/search/dfsselector.h"
#include "concolic/search/randomisedselector.h"
#include "concolic/search/roundrobinselector.h"

#include "concolicruntime.h"

namespace artemis
{


ConcolicRuntime::ConcolicRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
    , mTraceDisplay(options.outputCoverage != NONE)
    , mTraceDisplayOverview(options.outputCoverage != NONE)
    , mHandlerTracker(options.concolicEventHandlerReport)
    , mNumIterations(0)
{
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(postConcreteExecution(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));

    mManualEntryPoint = !options.concolicEntryPoint.isNull();
    mManualEntryPointXPath = options.concolicEntryPoint;

    // This web view is not used and not shown, but is required to give proper geometry to the ArtemisWebPage which
    // renders the site being tested. It is required to have proper geometry in order to click correctly on elements.
    // Without this the "bare" ArtemisWebPage is laid out correctly but the document element has zero size, so any
    // click is outside its boundary and is not recognised.
    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());
    //mWebView->resize(1000,1000);
    //mWebView->show();

    // The event detector for 'marker' events in the traces is created and connected here, as WebKitExecutor (where the rest are handled) does not know when these events happen.
    QSharedPointer<TraceMarkerDetector> markerDetector(new TraceMarkerDetector());
    QObject::connect(this, SIGNAL(sigNewTraceMarker(QString, QString, bool, SelectRestriction)),
                     markerDetector.data(), SLOT(slNewMarker(QString, QString, bool, SelectRestriction)));
    mWebkitExecutor->getTraceBuilder()->addDetector(markerDetector);

    QObject::connect(QWebExecutionListener::getListener(), SIGNAL(sigJavascriptSymbolicFieldRead(QString, bool)),
                     &mHandlerTracker, SLOT(slJavascriptSymbolicFieldRead(QString, bool)));
}

void ConcolicRuntime::run(const QUrl& url)
{
    mUrl = url;

    // We always run the first (no injection) load, to get the form fields and if necessary the entry-point.
    mRunningFirstLoad = true;
    mRunningWithInitialValues = false;

    mNextConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), url));

    mGraphOutputIndex = 1;
    mGraphOutputNameFormat = QString("tree-%1_%2%3-%4.gv").arg(QDateTime::currentDateTime().toString("yyyy-MM-dd-hh-mm-ss"));

    std::ofstream constraintLog;
    constraintLog.open("/tmp/constraintlog", std::ofstream::out | std::ofstream::app);

    constraintLog << "================================================================================\n";
    constraintLog << "Begin concolic analysis of " << url.toString().toStdString() << " at " << QDateTime::currentDateTime().toString("yyyy-MM-dd-hh-mm-ss").toStdString() << "\n";
    constraintLog << "\n";

    constraintLog.close();

    Log::info(QString("Concolic analysis of %1").arg(url.toString()).toStdString());

    preConcreteExecution();
}

void ConcolicRuntime::preConcreteExecution()
{
    if (mOptions.iterationLimit > 0 && mOptions.iterationLimit <= mNumIterations) {
        Log::info("Iteration limit reached");
        mNextConfiguration.clear();
    }

    if (mNextConfiguration.isNull()) {
        mHandlerTracker.writeGraph();
        mWebkitExecutor->detach();
        done();
        return;
    }

    if(mRunningFirstLoad){
        Log::debug("\n========== First-Load-Iteration =========");
        Log::info("Iteration 0: Form-field and entry-point finding");
    }else{
        if(mRunningWithInitialValues){
            Log::debug("\n=========== Initial-Iteration ===========");
            Log::info("Iteration 1: Submit with default values");
        }else{
            Log::debug("\n============= New-Iteration =============");
            Log::info(QString("Iteration %1:").arg(mNumIterations+1).toStdString());
        }
    }
    Log::debug("--------------- COVERAGE ----------------\n");
    Log::debug(mAppmodel->getCoverageListener()->toString().toStdString());

    mHandlerTracker.newIteration();

    mMarkerIndex = 1;
    mWebkitExecutor->executeSequence(mNextConfiguration); // calls the postSingleInjection, postAllinjection (via FormInputCollection) and postConcreteExecution methods as callback
}

void ConcolicRuntime::postAllInjection()
{
    // Update the form restrictions for the current DOM.
    mFormFieldRestrictions = FormFieldRestrictedValues::getRestrictions(mFormFields, mWebkitExecutor->getPage());

    if(mOptions.concolicTriggerEventHandlers) {
        // From here on, we will be triggering the button only.
        mHandlerTracker.beginHandler("Submit Button");
        emit sigNewTraceMarker("Clicking submit button", "B", false, SelectRestriction());
    }
}

void ConcolicRuntime::postSingleInjection(FormFieldDescriptorConstPtr field)
{
    // Update the form restrictions for the current DOM.
    mFormFieldRestrictions = FormFieldRestrictedValues::getRestrictions(mFormFields, mWebkitExecutor->getPage());

    if(mOptions.concolicTriggerEventHandlers) {
        // Find the identifier for this field
        QString identifier;
        if(field->getDomElement()->getId() != "") {
            identifier = field->getDomElement()->getId();
        } else {
            identifier = field->getDomElement()->getName();
        }
        QString label = QString("Trigger onchange for '%1'").arg(identifier);

        // Check if there is any form restriction relevant to this event (and should be added to the marker).
        // For now we only handle select restrictions.
        QPair<bool, SelectRestriction> restriction(false, SelectRestriction());
        restriction = FormFieldRestrictedValues::getRelevantSelectRestriction(mFormFieldRestrictions, identifier);

        // Add a marker to the trace
        mHandlerTracker.beginHandler(identifier);
        emit sigNewTraceMarker(label, QString::number(mMarkerIndex), restriction.first, restriction.second);

        // Trigger the handler
        QWebElement element = field->getDomElement()->getElement(mWebkitExecutor->getPage());
        FormFieldInjector::triggerChangeHandler(element);

        mMarkerIndex++;
    }
}

void ConcolicRuntime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    /*
     * We can be in three possible states.
     *  1. mRunningFirstLoad: A simple page load in which case we need to check for the entry points and choose one, and save the form fields.
     *  2. mRunningWithInitialValues: The initial form submission. use this to seed the trace tree then choose a target.
     *  3. Neither: A normal run, where we add to the tree and choose a new target.
     */

    if (mRunningFirstLoad){

        postInitialConcreteExecution(result); // Runs the next iteration itself.

    } else {
        // We already have an entry point.

        // Merge the new trace into the tree.
        // Sets up the search procedure and tree on the first run (when mRunningWithInitialValues is set).
        mergeTraceIntoTree();

        // Choose the next node to explore
        chooseNextTargetAndExplore();

    }

    mNumIterations++;
}






// Utility method to output the tree graph at each step.
void ConcolicRuntime::outputTreeGraph()
{
    if(mOptions.concolicTreeOutput == TREE_NONE){
        return;
    }
    // Output the graphs, and if we are in TREE_FINAL mode, then delete the older ones.
    // We do it like this to make sure there is always an up-to-date version of the tree saved out either for
    // viewing the progress or in case of crashes.

    // We want all the graphs from a certain run to have the same "base" name and an increasing index, so they can be easily grouped.
    QString name = mGraphOutputNameFormat.arg("").arg(mNumIterations).arg(mGraphOutputIndex);
    QString name_min = mGraphOutputNameFormat.arg("min_").arg(mNumIterations).arg(mGraphOutputIndex);
    Log::debug(QString("CONCOLIC-INFO: Writing tree to file %1").arg(name).toStdString());
    mGraphOutputIndex++;

    QString previous_name = mGraphOutputPreviousName;
    QString previous_name_min = mGraphOutputOverviewPreviousName;

    mTraceDisplay.writeGraphFile(mSymbolicExecutionGraph, name, false);
    mGraphOutputPreviousName = name;
    if(mOptions.concolicTreeOutputOverview){
        mTraceDisplayOverview.writeGraphFile(mSymbolicExecutionGraph, name_min, false);
        mGraphOutputOverviewPreviousName = name_min;
    }

    if(mOptions.concolicTreeOutput == TREE_FINAL){
        // Delete the older graph files.
        if(!previous_name.isEmpty()){ // Empty if we have not written a graph yet.
            QFile::remove(previous_name);
        }
        if(!previous_name_min.isEmpty()){ // Empty if we have not written a graph yet.
            QFile::remove(previous_name_min);
        }
    }
}




// Given a FormInput, create an event sequence which will use that input and fire the entry point handler.
// Sets mNextConfiguration.
void ConcolicRuntime::setupNextConfiguration(QSharedPointer<FormInputCollection> formInput)
{
    BaseInputConstPtr submitEvent;

    // Depending on whether we have a manual or auto-detected entry point, create a suitable input type.
    if(mManualEntryPoint){
        // Create a ClickInput which will inject the FormInputCollection and click on the given coordinates.
        submitEvent = BaseInputConstPtr(new ClickInput(mManualEntryPointXPath, formInput));
    }else{
        assert(!mEntryPointEvent.isNull());

        // Create a suitable EventParameters object for this submission. (As in StaticEventParameterGenerator.)
        EventParametersConstPtr eventParameters = EventParametersConstPtr(new MouseEventParameters(mEntryPointEvent->getName(), true, true, 1, 0, 0, 0, 0, false, false, false, false, 0));

        // Create a suitable TargetDescriptor object for this submission.
        // TODO: No support for JQuery unless we use a JQueryTarget, JQueryListener (and TargetGenerator?).
        TargetDescriptorConstPtr targetDescriptor = TargetDescriptorConstPtr(new LegacyTarget(mEntryPointEvent));

        // Create a DomInput which will inject the FormInputCollection and fire the entry point event.
        submitEvent = BaseInputConstPtr(new DomInput(mEntryPointEvent, formInput, eventParameters, targetDescriptor, mExecStat));
    }

    // Create an input sequence consisting of just this event.
    QList<QSharedPointer<const BaseInput> > inputList;
    inputList.append(submitEvent);
    InputSequenceConstPtr inputSequence = InputSequenceConstPtr(new InputSequence(inputList));

    // Create an executableConfiguration from this input sequence.
    mNextConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(inputSequence, mUrl));

    Log::debug("Next configuration is:");
    Log::debug(mNextConfiguration->toString().toStdString());
}


// Does the processing after the very first page load, to prepare for the testing.
void ConcolicRuntime::postInitialConcreteExecution(QSharedPointer<ExecutionResult> result)
{
    // Find the form fields on the page and save them.
    mFormFields = result->getFormFields();
    mFormFieldRestrictions = FormFieldRestrictedValues::getRestrictions(mFormFields, mWebkitExecutor->getPage());

    // Print the form fields found on the page.
    Log::debug("Form fields found:");
    QStringList fieldNames;
    foreach(QSharedPointer<const FormFieldDescriptor> field, mFormFields){
        fieldNames.append(field->getDomElement()->toString());
    }
    Log::info(QString("  Form fields: %1").arg(fieldNames.join(", ")).toStdString());

    // Print the form field restrictions found.
    QStringList options;
    Log::debug("Form field SELECT restrictions found:");
    if (mFormFieldRestrictions.first.size() == 0) {
        Log::debug("  None");
    }
    foreach (SelectRestriction sr, mFormFieldRestrictions.first) {
        int idx = 0;
        foreach(QString val, sr.values) {
            options.append(QString("%1/'%2'").arg(idx).arg(val));
            idx++;
        }
        Log::debug(QString("  '%1' chosen from: %2").arg(sr.variable).arg(options.join(", ")).toStdString());
    }

    Log::debug("Form field RADIO restrictions found:");
    if (mFormFieldRestrictions.second.size() == 0) {
        Log::debug("  None");
    }
    foreach (RadioRestriction rr, mFormFieldRestrictions.second) {
        options = rr.variables.toList();
        Log::debug(QString("  '%1' mutually exclusive%2: %3").arg(rr.groupName).arg(rr.alwaysSet ? "" : " (or none)").arg(options.join(", ")).toStdString());
    }

    // Create an "empty" form input which will inject nothing into the page.
    QList<FormInputPair > inputs;
    FormInputCollectionPtr formInput = FormInputCollectionPtr(new FormInputCollection(inputs, true, mFormFields));
    // Connect it to our slots so we will know when the injection is performed.
    QObject::connect(formInput.data(), SIGNAL(sigFinishedWriteToPage()),
                     this, SLOT(postAllInjection()));
    QObject::connect(formInput.data(), SIGNAL(sigInjectedToField(FormFieldDescriptorConstPtr)),
                     this, SLOT(postSingleInjection(FormFieldDescriptorConstPtr)));

    // On the next iteration, we will be running with initial values.
    mRunningFirstLoad = false;
    mRunningWithInitialValues = true;

    // If we are using automatic entry-point finding, then detect them here.
    // If we use a manual XPath then we don't need to do anything about entry-points yet, it is dealt with in ClickInput.
    if(!mManualEntryPoint){

        Log::debug("Analysing page entrypoints...");

        // Choose and save the entry point for use in future runs.
        MockEntryPointDetector detector(mWebkitExecutor->getPage());
        mEntryPointEvent = detector.choose(result);

        if(mEntryPointEvent){
            Log::debug(QString("Chose entry point %1").arg(mEntryPointEvent->toString()).toStdString());
            Log::info(QString("  Entry point: %1").arg(mEntryPointEvent->toString()).toStdString());

        }else{
            Log::debug("\n========== No Entry Points ==========");
            Log::debug("Could not find any suitable entry point for the analysis on this page. Exiting.");
            Log::info("No entry points detected.");

            mWebkitExecutor->detach();
            done();
            return;
        }

    }else{
        Log::info(QString("  Entry point: %1").arg(mManualEntryPointXPath).toStdString());
    }

    // Create the new event sequence and set mNextConfiguration.
    setupNextConfiguration(formInput);

    // Execute the next configuration.
    preConcreteExecution();
}


// Creates the tree and sets up the search procedure and merges new traces into the tree.
void ConcolicRuntime::mergeTraceIntoTree()
{
    // First, we classify the trace which just ran.
    // This can  modify it to add the correct end marker to the trace.
    TraceNodePtr trace = mWebkitExecutor->getTraceBuilder()->trace();

    switch(mTraceClassifier.classify(trace)){
    case SUCCESS:
        Log::info("  Recorded trace was classified as a SUCCESS.");
        break;
    case FAILURE:
        Log::info("  Recorded trace was classified as a FAILURE.");
        break;
    default:
        Log::info("  Recorded trace was classified as UNKNOWN.");
    }


    // Now we must merge this trace into the tree.
    if (mRunningWithInitialValues){
        // After the very first run we need to set up the tree & search procedure.
        // We can't just begin with an empty tree and merge every trace in, as the search procedure needs a
        // pointer to the tree, which will be replaced in that case.
        // If this is a problem, we could just introduce a header node for trees.
        mSymbolicExecutionGraph = trace;
        mRunningWithInitialValues = false;

        switch(mOptions.concolicSearchProcedure) {
        case SEARCH_DFS:
            mSearchStrategy = TreeSearchPtr(new DepthFirstSearch(mSymbolicExecutionGraph,
                                                                 mOptions.concolicDfsDepthLimit,
                                                                 mOptions.concolicDfsRestartLimit));
            break;

        case SEARCH_SELECTOR:
            mSearchStrategy = TreeSearchPtr(new RandomAccessSearch(mSymbolicExecutionGraph,
                                                                   buildSelector(mOptions.concolicSearchSelector),
                                                                   mOptions.concolicSearchBudget));
            QObject::connect(&mTraceMerger, SIGNAL(sigTraceJoined(TraceNodePtr, int, TraceNodePtr, TraceNodePtr)),
                             mSearchStrategy.dynamicCast<RandomAccessSearch>().data(), SLOT(slNewTraceAdded(TraceNodePtr, int, TraceNodePtr, TraceNodePtr)));
            break;

        default:
            Log::fatal("Unknown search procedure.");
            exit(1);
        }

        Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);

    } else {

        // A normal run.
        // Merge trace with tracegraph
        mSymbolicExecutionGraph = mTraceMerger.merge(trace, mSymbolicExecutionGraph);

        // Check if we actually explored the intended target.
        if(mSearchStrategy->overUnexploredNode()){
            mSearchStrategy->markNodeMissed();
            Log::info("  Recorded trace did not take the expected path.");
        }
    }

    // Dump the current state of the tree to a file.
    outputTreeGraph();
}


// Prints the solution from the solver.
void ConcolicRuntime::printSolution(SolutionPtr solution, QStringList varList)
{
    foreach(QString var, varList){
        Symbolvalue value = solution->findSymbol(var);
        if(value.found){
            switch (value.kind) {
            case Symbolic::INT:
                Log::info(QString("    %1 = %2").arg(var).arg(value.u.integer).toStdString());
                break;
            case Symbolic::BOOL:
                Log::info(QString("    %1 = %2").arg(var).arg(value.u.boolean ? "true" : "false").toStdString());
                break;
            case Symbolic::STRING:
                if(value.string.empty()){
                    Log::info(QString("    %1 = \"\"").arg(var).toStdString());
                }else{
                    Log::info(QString("    %1 = \"%2\"").arg(var).arg(value.string.c_str()).toStdString());
                }
                break;
            default:
                Log::fatal(QString("Unimplemented value type encountered for variable %1 (%2)").arg(var).arg(value.kind).toStdString());
                exit(1);
            }
        }else{
            Log::fatal(QString("Error: Could not find value for %1 in the solver's solution.").arg(var).toStdString());
            exit(1); // TODO: Maybe this should just be "could not solve" instead?
        }
    }
}

QSharedPointer<FormInputCollection> ConcolicRuntime::createFormInput(QMap<QString, Symbolic::SourceIdentifierMethod> freeVariables, SolutionPtr solution)
{
    QStringList varList = freeVariables.keys();

    // For each symbolic variable, attempt to match it with a FormField object from the initial run.
    Log::debug("Next form value injections are:");
    QList<FormInputPair> inputs;

    foreach(QString varName, varList){
        Symbolvalue value = solution->findSymbol(varName);
        if(!value.found){
            Log::error(QString("Error: Could not find value for %1 in the solver's solution.").arg(varName).toStdString());
            Statistics::statistics()->accumulate("Concolic::FailedInjections", 1);
            continue;
        }

        // Find the corresponding FormField by searching on the relevant attribute.
        QSharedPointer<const FormFieldDescriptor> varSourceField = findFormFieldForVariable(varName, freeVariables.value(varName));
        // May be null if we failed to inject.
        if(varSourceField.isNull()){
            // Error already logged within findFormFieldForVariable.
            continue;
        }

        // Create the field/value pairing to be injected using the FormInput object.
        switch (value.kind) {
        case Symbolic::BOOL:
            inputs.append(FormInputPair(varSourceField, InjectionValue(value.u.boolean)));
            Log::debug(QString("Injecting boolean %1 into %2").arg(value.u.boolean ? "true" : "false").arg(varName).toStdString());
            break;
        case Symbolic::STRING:
            inputs.append(FormInputPair(varSourceField, InjectionValue(QString::fromStdString(value.string))));
            Log::debug(QString("Injecting string '%1' into %2").arg(QString(value.string.c_str())).arg(varName).toStdString());
            break;
        case Symbolic::INT:
            inputs.append(FormInputPair(varSourceField, InjectionValue(value.u.integer)));
            Log::debug(QString("Injecting int %1 into %2").arg(value.u.integer).arg(varName).toStdString());
            break;
        default:
            Log::error(QString("INJECTION ERROR: Unimplemented value type encountered for variable %1 (%2)").arg(varName).arg(value.kind).toStdString());
            Statistics::statistics()->accumulate("Concolic::FailedInjections", 1);
            continue;
        }

    }

    // Set up a new configuration which tests this input.
    QSharedPointer<FormInputCollection> formInput = QSharedPointer<FormInputCollection>(new FormInputCollection(inputs, true, mFormFields));
    // Connect it to our slots so we will know when the injection is performed.
    QObject::connect(formInput.data(), SIGNAL(sigFinishedWriteToPage()),
                     this, SLOT(postAllInjection()));
    QObject::connect(formInput.data(), SIGNAL(sigInjectedToField(FormFieldDescriptorConstPtr)),
                     this, SLOT(postSingleInjection(FormFieldDescriptorConstPtr)));

    return formInput;
}


// Given a symbolic variable, find the corresponding form field on the page.
QSharedPointer<const FormFieldDescriptor> ConcolicRuntime::findFormFieldForVariable(QString varName, Symbolic::SourceIdentifierMethod varSourceIdentifierMethod)
{
    QSharedPointer<const FormFieldDescriptor> varSourceField;

    // Variable names are of the form SYM_IN_<name>, and we will need to use <name> directly when searching the ids and names of the form fields.
    // Bool and int variables can also have a marker to distinguish them from other variables from the same element.
    QString varBaseName = varName;
    varBaseName.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

    // TODO: There is similar code in formfieldrestrictedvalues.cpp, which could be merged into a single utility.
    switch(varSourceIdentifierMethod){
    case Symbolic::INPUT_NAME:
        // Fetch the formField with this name
        foreach(QSharedPointer<const FormFieldDescriptor> field, mFormFields){
            if(field->getDomElement()->getName() == varBaseName){
                varSourceField = field;
                break;
            }
        }
        break;

    case Symbolic::ELEMENT_ID:
        // Fetch the form field with this id (or Artemis ID)
        foreach(QSharedPointer<const FormFieldDescriptor> field, mFormFields){
            if(field->getDomElement()->getId() == varBaseName){
                varSourceField = field;
                break;
            }
        }
        break;

    default:
        Log::error("Error: Unexpected identification method for form fields encountered.");
        Statistics::statistics()->accumulate("Concolic::FailedInjections", 1);
        return varSourceField; // Returning null to signify error.
    }

    // Check that we found a FormField.
    if(varSourceField.isNull()){
        Log::error(QString("Error: Could not identify a form field for %1.").arg(varName).toStdString());
        Statistics::statistics()->accumulate("Concolic::FailedInjections", 1);
        return varSourceField; // Returning null to signify error.
    }

    return varSourceField;
}


// Generates a new solution from the path condition and runs it.
void ConcolicRuntime::exploreNextTarget()
{
    PathConditionPtr target = mSearchStrategy->getTargetPC();
    QSet<SelectRestriction> dynamicSelectConstraints = mSearchStrategy->getTargetDomConstraints();

    // If the returned PC is empty, then there were no solvable constraints on the path.
    if(target->size() < 1) {
        mSearchStrategy->markNodeUnsolvable();
        Log::info("  Could not solve constraint:");
        Log::info("    All branches on path were known to be difficult.");
        Log::debug("Skipping this target!");
        // Dump the current state of the tree to a file.
        outputTreeGraph();
        // Skip this node and move on to the next.
        chooseNextTargetAndExplore();
        return;
    }

    // TODO: Currently only select constraints are handled dynamically, so we need to merge them with the static radio button constraints.
    FormRestrictions dynamicRestrictions = mergeDynamicSelectRestrictions(mFormFieldRestrictions, dynamicSelectConstraints);

    Log::info("  Next target:");
    QString targetString = QString("    ") + QString::fromStdString(target->toStatisticsValuesString(true)).trimmed();
    targetString.replace('\n', "\n    ");
    Log::info(targetString.toStdString());

    // Get (and print) the list of free variables in the target PC.
    QMap<QString, Symbolic::SourceIdentifierMethod> freeVariables = target->freeVariables();
    QStringList varList = freeVariables.keys();

    Log::debug(QString("Variables we need to solve (%1):").arg(varList.length()).toStdString());
    Log::debug(varList.join(", ").toStdString());

    // Try to solve this PC to get some concrete input.
    SolverPtr solver = getSolver(mOptions);
    SolutionPtr solution = solver->solve(target, dynamicRestrictions);

    if(solution->isSolved()) {
        Log::debug("Solved the target PC:");
        Log::info("  Next injection:");

        // Print this solution
        printSolution(solution, varList);


        QSharedPointer<FormInputCollection> formInput = createFormInput(freeVariables, solution);
        setupNextConfiguration(formInput);

        // Execute next iteration
        preConcreteExecution();

    }else{
        // Mark the current node as unsolvable.
        // If it was solved but unsatisfiable, then mark it as UNSAT instead.
        if(solution->isUnsat()){
            mSearchStrategy->markNodeUnsat();
            Log::info("  Constraint is UNSAT.");
        }else{
            // Check if there was a specific clause which caused this PC to be unsolvable and mark it as difficult.
            if(solution->getUnsolvableClause() >= 0) {
                TraceSymbolicBranch* difficultBranch = target->getBranch(solution->getUnsolvableClause());
                assert(!difficultBranch->isDifficult()); // We should never have tried to solve a known difficult branch. Otherwise we may get stuck in a loop when we retry!
                difficultBranch->markDifficult();
                Statistics::statistics()->accumulate("Concolic::ExecutionTree::DifficultBranches", 1);
            }

            // We must give up in the following cases:
            //    * There was no bad clause identified
            //    * The bad clause was from the node we were directly targeting
            // Otherwise we can re-try writing the PC without this difficult clause.
            if (solution->getUnsolvableClause() < 0 || (uint)solution->getUnsolvableClause() == target->size()-1) {
                mSearchStrategy->markNodeUnsolvable();
                Log::info("  Could not solve constraint:");
                Log::info(QString("    %1").arg(solution->getUnsolvableReason()).toStdString());

            } else {
                Log::info("  Could not solve this constraint. Re-trying after marking as difficult.");
                Statistics::statistics()->accumulate("Concolic::DifficultBranchRetries", 1);
                exploreNextTarget(); // N.B. the call to Search::getTargetPC() will return an updated PC if the tree has been modified to mark a node as difficult.
            }
        }
        Log::debug("Skipping this target!");

        // Dump the current state of the tree to a file.
        outputTreeGraph();

        // Skip this node and move on to the next.
        chooseNextTargetAndExplore();
    }
}

FormRestrictions ConcolicRuntime::mergeDynamicSelectRestrictions(FormRestrictions base, QSet<SelectRestriction> replacements)
{
    // Copy the radio constraints across as-is, they are not handled dynamically yet.
    // Merge in the updated constraints from the search procedure with the latest "default" ones from base.

    FormRestrictions updated = base;
    updated.first = replacements;

    QSet<QString> replacementVariables;
    foreach(SelectRestriction sr, replacements) {
        qDebug() << "We have an updated value for" << sr.variable;
        replacementVariables.insert(sr.variable);
    }

    foreach(SelectRestriction sr, base.first) {
        if (!replacementVariables.contains(sr.variable)) {
            qDebug() << "Using the default value for value for" << sr.variable;
            updated.first.insert(sr);
        }
    }

    return updated;
}


// Uses the search strategy to choose a new target and then explore it.
void ConcolicRuntime::chooseNextTargetAndExplore()
{
    // Choose the next target.
    if(mSearchStrategy->chooseNextTarget()){
        // Runs the next execution itself.
        exploreNextTarget();

    }else{
        outputTreeGraph();

        Log::debug("\n============= Finished Search ==============");
        Log::info("Finished serach of the tree.");

        mHandlerTracker.writeGraph();
        mWebkitExecutor->detach();
        done();
        return;
    }
}

void ConcolicRuntime::reportStatistics()
{
    Statistics::statistics()->accumulate("Concolic::Iterations", mNumIterations);

    if(mSymbolicExecutionGraph.isNull()) {
        return;
    }

    TraceStatistics stats;
    stats.processTrace(mSymbolicExecutionGraph);

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::ConcreteBranchesTotal", stats.mNumConcreteBranches);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::ConcreteBranchesFullyExplored", stats.mNumConcreteBranchesFullyExplored);

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::SymbolicBranchesTotal", stats.mNumSymBranches);
    Statistics::statistics()->accumulate("Concolic::ExecutionTree::SymbolicBranchesFullyExplored", stats.mNumSymBranchesFullyExplored);

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::Alerts", stats.mNumAlerts);
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

    Statistics::statistics()->accumulate("Concolic::EventSequence::HandlersTriggered", mFormFields.size());
    Statistics::statistics()->accumulate("Concolic::EventSequence::SymbolicBranchesTotal", stats.mNumEventSequenceSymBranches);
    Statistics::statistics()->accumulate("Concolic::EventSequence::SymbolicBranchesFullyExplored", stats.mNumEventSequenceSymBranchesFullyExplored);
}


AbstractSelectorPtr ConcolicRuntime::buildSelector(ConcolicSearchSelector description)
{
    AbstractSelectorPtr selector;
    QList<AbstractSelectorPtr> children;

    switch(description.type) {
    case ConcolicSearchSelector::SELECTOR_DFS:
        selector = AbstractSelectorPtr(new DFSSelector());
        break;
    case ConcolicSearchSelector::SELECTOR_RANDOM:
        selector = AbstractSelectorPtr(new RandomisedSelector());
        break;
    case ConcolicSearchSelector::SELECTOR_AVOID_UNSAT:
        selector = AbstractSelectorPtr(new AvoidUnsatSelector());
        break;
    case ConcolicSearchSelector::SELECTOR_ROUND_ROBIN:
        foreach(ConcolicSearchSelector childDescription, description.components) {
            children.append(buildSelector(childDescription));
        }
        selector = AbstractSelectorPtr(new RoundRobinSelector(children));
        break;
    default:
        Log::fatal("ERROR: Unsupported choice of concolic-selection-procedure.");
        exit(1);
    }

    return selector;
}


void ConcolicRuntime::done()
{
    reportStatistics();
    Runtime::done();
}


} // namespace artemis

