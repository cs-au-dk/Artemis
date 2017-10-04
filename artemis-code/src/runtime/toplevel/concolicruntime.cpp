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
#include "util/fileutil.h"
#include "concolic/traceeventdetectors.h"
#include "statistics/statsstorage.h"
#include "concolic/executiontree/classifier/formsubmissionclassifier.h"
#include "concolic/executiontree/classifier/jserrorclassifier.h"
#include "concolic/executiontree/classifier/nullclassifier.h"

#include "concolicruntime.h"

namespace artemis
{


ConcolicRuntime::ConcolicRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
    , mConcolicAnalysis(new ConcolicAnalysis(options, ConcolicAnalysis::CONCOLIC_RUNTIME))
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

    // Link the ConcolicAnalysis signals.
    QObject::connect(mConcolicAnalysis.data(), SIGNAL(sigExecutionTreeUpdated(TraceNodePtr, QString)),
                     this, SLOT(slExecutionTreeUpdated(TraceNodePtr, QString)));

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
        mHandlerTracker.writeGraph(mFormFieldPermutation);
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

        mFormFieldRestrictions = mFormFieldInitialRestrictions; // Prevents noticing a change between the end of one execution and the start of the next.
    }
    Log::debug("--------------- COVERAGE ----------------\n");
    Log::debug(mAppmodel->getCoverageListener()->toString().toStdString());

    mHandlerTracker.newIteration();

    mMarkerIndex = 0;
    mWebkitExecutor->executeSequence(mNextConfiguration); // calls the postSingleInjection, postAllinjection (via FormInputCollection) and postConcreteExecution methods as callback
}

void ConcolicRuntime::postAllInjection()
{
    updateFormFieldRestrictionsForCurrentDom();

    if(mOptions.concolicTriggerEventHandlers) {

        // If synchronised injections are disabled then trigger all the events here (after all the injections).
        if(mOptions.concolicDisabledFeatures.testFlag(EVENT_SEQUENCE_SYNC_INJECTIONS)) {
            foreach(FormFieldDescriptorConstPtr field, mFormFields) {
                Statistics::statistics()->accumulate("Concolic::EventSequence::ChangeHandlersTriggeredAfterInjection", 1);
                triggerFieldChangeHandler(field);
            }
        }

        // From here on, we will be triggering the button only.
        mHandlerTracker.beginHandler("Submit Button");
        emit sigNewTraceMarker("Clicking submit button", "B", false, SelectRestriction());
    }
}

void ConcolicRuntime::postSingleInjection(FormFieldDescriptorConstPtr field)
{
    updateFormFieldRestrictionsForCurrentDom();

    if(mOptions.concolicTriggerEventHandlers &&
            !mOptions.concolicDisabledFeatures.testFlag(EVENT_SEQUENCE_SYNC_INJECTIONS)) {
        Statistics::statistics()->accumulate("Concolic::EventSequence::ChangeHandlersTriggeredInSync", 1);
        triggerFieldChangeHandler(field);
    }
}

void ConcolicRuntime::triggerFieldChangeHandler(FormFieldDescriptorConstPtr field)
{
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
    QString idxStr = mMarkerIndex < mFormFieldPermutation.length() ? QString::number(mFormFieldPermutation.at(mMarkerIndex)) : "?";
    emit sigNewTraceMarker(label, idxStr, restriction.first, restriction.second);

    // Trigger the handler
    QWebElement element = field->getDomElement()->getElement(mWebkitExecutor->getPage());
    FormFieldInjector::triggerChangeHandler(element);

    mMarkerIndex++;
}

void ConcolicRuntime::updateFormFieldRestrictionsForCurrentDom()
{
    FormRestrictions oldRestrictions = mFormFieldRestrictions;

    mFormFieldRestrictions = FormFieldRestrictedValues::getRestrictions(mFormFields, mWebkitExecutor->getPage());

    if(oldRestrictions != mFormFieldRestrictions) {
        Statistics::statistics()->accumulate("Concolic::Solver::DomConstraintsUpdatedDynamically", 1);
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



void ConcolicRuntime::slExecutionTreeUpdated(TraceNodePtr tree, QString name)
{
    outputTreeGraph();
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

    mTraceDisplay.writeGraphFile(mConcolicAnalysis->getExecutionTree(), name, false);
    mGraphOutputPreviousName = name;
    if(mOptions.concolicTreeOutputOverview){
        mTraceDisplayOverview.writeGraphFile(mConcolicAnalysis->getExecutionTree(), name_min, false);
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
        TargetDescriptorConstPtr targetDescriptor = mTargetGenerator->generateTarget(mEntryPointEvent);

        // Create a DomInput which will inject the FormInputCollection and fire the entry point event.
        submitEvent = BaseInputConstPtr(new DomInput(mEntryPointEvent, formInput, eventParameters, targetDescriptor, mExecStat));
    }

    // Create an input sequence consisting of just this event.
    QList<QSharedPointer<const BaseInput> > inputList;
    inputList.append(submitEvent);
    InputSequenceConstPtr inputSequence = InputSequenceConstPtr(new InputSequence(inputList));

    // Create an executableConfiguration from this input sequence.
    QUrl url = mUrl;
    if (mOptions.testingConcolicSendIterationCountToServer) {
        QList<QPair<QString, QString> > query;
        query.append(QPair<QString, QString>("ArtemisIteration", QString::number(mNumIterations)));
        url.setQueryItems(query);
    }
    mNextConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(inputSequence, url));

    Log::debug("Next configuration is:");
    Log::debug(mNextConfiguration->toString().toStdString());
}


// Does the processing after the very first page load, to prepare for the testing.
void ConcolicRuntime::postInitialConcreteExecution(QSharedPointer<ExecutionResult> result)
{
    // Find the form fields on the page and save them.
    mFormFields = permuteFormFields(result->getFormFields(), mOptions.concolicEventHandlerPermutation);
    mFormFieldRestrictions = FormFieldRestrictedValues::getRestrictions(mFormFields, mWebkitExecutor->getPage());
    mFormFieldInitialRestrictions = mFormFieldRestrictions;
    mConcolicAnalysis->setFormRestrictions(mFormFieldInitialRestrictions);

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

// Re-orders the form fields list given the permutation supplied as an argument.
// Format should be "[2,4,3,1]" but validity needs to be checked here.
QList<FormFieldDescriptorConstPtr> ConcolicRuntime::permuteFormFields(QList<FormFieldDescriptorConstPtr> fields, QString permutation)
{
    // If the string is empty, no permutation was specified.
    if(permutation.isEmpty()) {
        QList<int> noPerm;
        for(int i = 0; i < fields.length(); i++) {
            noPerm.append(i+1);
        }

        mFormFieldPermutation = noPerm;
        return fields;
    }

    // Decode the permutation
    QRegExp validFormat("\\[\\d((,|\\d)*\\d)?\\]");
    permutation.replace(' ', "");
    if(!validFormat.exactMatch(permutation)) {
        Log::fatal("Error in concolic-event-sequence-permutation (invalid format).");
        Log::fatal(permutation.toStdString());
        exit(1);
    }

    permutation.replace('[', "");
    permutation.replace(']', "");
    QStringList elements = permutation.split(',');
    QList<int> reordering;
    int x;
    foreach(QString el, elements) {
        x = el.toInt();
        if(x == 0) {
            // 0 or error decoding.
            Log::fatal("Error in concolic-event-sequence-permutation (found 0 or failed to decode a value).");
            Log::fatal(permutation.toStdString());
            exit(1);
        }
        reordering.append(x);
    }

    // Check the size is valid (not longer than the original list)
    if(reordering.length() > fields.length()) {
        Log::fatal("Error in concolic-event-sequence-permutation (too long).");
        Log::fatal(permutation.toStdString());
        exit(1);
    }

    // Check that the values are valid (all refer to an appropriate index)
    foreach(int handler, reordering) {
        if(handler <= 0 || handler > fields.length()) { // handlers are 1-indexed.
            Log::fatal("Error in concolic-event-sequence-permutation (index out of range).");
            Log::fatal(permutation.toStdString());
            exit(1);
        }
    }

    // Check that it is a valid permutation (unique values)
    if(reordering.length() != reordering.toSet().size()) {
        Log::fatal("Error in concolic-event-sequence-permutation (repeated index).");
        Log::fatal(permutation.toStdString());
        exit(1);
    }

    // Apply the permutation
    QList<FormFieldDescriptorConstPtr> result;
    foreach(int idx, reordering) {
        result.append(fields.at(idx - 1)); // Permutations are numbered from 1, not from 0.
    }

    mFormFieldPermutation = reordering;
    return result;
}


// Creates the tree and sets up the search procedure and merges new traces into the tree.
void ConcolicRuntime::mergeTraceIntoTree()
{
    // First, we classify the trace which just ran.
    // This can  modify it to add the correct end marker to the trace.
    TraceNodePtr trace = mWebkitExecutor->getTraceBuilder()->trace();

    TraceClassificationResult classification = mTraceClassifier->classify(trace);

    switch(classification){
    case SUCCESS:
        Log::info("  Recorded trace was classified as a SUCCESS.");
        break;
    case FAILURE:
        Log::info("  Recorded trace was classified as a FAILURE.");
        break;
    default:
        Log::info("  Recorded trace was classified as UNKNOWN.");
    }

    logInjectionValues(classification);

    ConcolicAnalysis::ExplorationHandle exploration = mRunningWithInitialValues ? ConcolicAnalysis::NO_EXPLORATION_TARGET : mExplorationResult.target;
    mConcolicAnalysis->addTrace(trace, exploration);

    // Once we have done at least one merge, the we are now into the "main" analysis.
    mRunningWithInitialValues = false;
}


// Prints the solution from the solver.
void ConcolicRuntime::printSolution(SolutionPtr solution, QStringList varList)
{
    Log::info("  Next injection:");

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
        InjectionValue iv;
        switch (value.kind) {
        case Symbolic::BOOL:
            iv = InjectionValue(value.u.boolean);
            inputs.append(FormInputPair(varSourceField, iv));
            Log::debug(QString("Injecting boolean %1 into %2").arg(value.u.boolean ? "true" : "false").arg(varName).toStdString());
            break;
        case Symbolic::STRING:
            iv = InjectionValue(QString::fromStdString(value.string));
            inputs.append(FormInputPair(varSourceField, iv));
            Log::debug(QString("Injecting string '%1' into %2").arg(QString(value.string.c_str())).arg(varName).toStdString());
            break;
        case Symbolic::INT:
            iv = InjectionValue(value.u.integer);
            inputs.append(FormInputPair(varSourceField, iv));
            Log::debug(QString("Injecting int %1 into %2").arg(value.u.integer).arg(varName).toStdString());
            break;
        default:
            Log::error(QString("INJECTION ERROR: Unimplemented value type encountered for variable %1 (%2)").arg(varName).arg(value.kind).toStdString());
            Statistics::statistics()->accumulate("Concolic::FailedInjections", 1);
            continue;
        }

        QString varBaseName = varName;
        varBaseName.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));
        mPreviousInjections.insert(varBaseName, iv);

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
    assert(mExplorationResult.newExploration);
    assert(mExplorationResult.solution->isSolved());

    Log::debug("Solved the target PC:");

    SolutionPtr solution = mExplorationResult.solution;

    // Get the list of free variables in the target PC.
    QMap<QString, Symbolic::SourceIdentifierMethod> injectionVariables = mExplorationResult.pc->freeVariables();
    QStringList varList = injectionVariables.keys();

    // TODO: There is no longer really any reason to differentiate between variables from the PC and those introduced by the solver. This code could be combined and we would not need to read the PC back from the ExplorationResult.

    // Check if there are any variables in the solution which were not originally in the PC.
    // This can happen (e.g.) with radio button constraints, and these MUST be included in the injection.
    injectionVariables.unite(getExtraSolutionVariables(solution, varList));
    varList = injectionVariables.keys();

    // Print this solution
    printSolution(solution, varList);

    QSharedPointer<FormInputCollection> formInput = createFormInput(injectionVariables, solution);
    setupNextConfiguration(formInput);

    // Execute next iteration
    preConcreteExecution();
}

QMap<QString, Symbolic::SourceIdentifierMethod> ConcolicRuntime::getExtraSolutionVariables(SolutionPtr solution, QStringList expected)
{
    // If there are any variables in solution which are not listed in expected, then look up their SourceIdentifierMethod and return them.
    QMap<QString, Symbolic::SourceIdentifierMethod> result;
    QString baseName;
    bool found;
    Symbolic::SourceIdentifierMethod method = Symbolic::ELEMENT_ID; // Initial value to remove warning.

    foreach (QString symbol, solution->symbols()) {
        if (!expected.contains(symbol)) {
            // This is a new variable from the solver.
            // We can't know the SourceIdentifierMethod, so search for the element in the list of form fields.

            baseName = symbol;
            baseName.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));
            found = false;

            // Check for matching ID.
            foreach (FormFieldDescriptorConstPtr field, mFormFields) {
                if (field->getDomElement()->getId() == baseName) {
                    found = true;
                    method = Symbolic::ELEMENT_ID;
                    break;
                }
            }

            // Check for mathcing name
            if (!found) {
                foreach (FormFieldDescriptorConstPtr field, mFormFields) {
                    if (field->getDomElement()->getName() == baseName) {
                        found = true;
                        method = Symbolic::INPUT_NAME;
                        break;
                    }
                }
            }

            // If nothing was found it is an error.
            if (!found) {
                Log::fatal("Error: Found a variable in the solution which was not in the PC and could not be found in the DOM.");
                Log::fatal(symbol.toStdString());
                exit(1);
            }

            result.insert(symbol, method);
        }
    }

    return result;
}


// Uses the search strategy to choose a new target and then explore it.
void ConcolicRuntime::chooseNextTargetAndExplore()
{
    mExplorationResult = mConcolicAnalysis->nextExploration();

    if (mExplorationResult.newExploration) {

        // Runs the next execution itself.
        exploreNextTarget();

    } else {

        outputTreeGraph();

        Log::debug("\n============= Finished Search ==============");
        Log::info("Finished serach of the tree.");

        mHandlerTracker.writeGraph(mFormFieldPermutation);
        mWebkitExecutor->detach();
        done();
        return;
    }
}

// TODO: This function is duplicated in concolicstandaloneruntime.cpp.
void ConcolicRuntime::reportStatistics()
{
    Statistics::statistics()->accumulate("Concolic::Iterations", mNumIterations);

    if(mConcolicAnalysis->getExecutionTree().isNull()) {
        return;
    }

    TraceStatistics stats;
    stats.processTrace(mConcolicAnalysis->getExecutionTree());

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

    Statistics::statistics()->accumulate("Concolic::EventSequence::HandlersTriggered", mFormFields.size());
    Statistics::statistics()->accumulate("Concolic::EventSequence::SymbolicBranchesTotal", stats.mNumEventSequenceSymBranches);
    Statistics::statistics()->accumulate("Concolic::EventSequence::SymbolicBranchesFullyExplored", stats.mNumEventSequenceSymBranchesFullyExplored);

    mHandlerTracker.reportGraphStatistics();
}


// Write the injection logs to a file /tmp/injections/*
void ConcolicRuntime::logInjectionValues(TraceClassificationResult classification)
{
    QString entryPoint = mManualEntryPoint ? mManualEntryPointXPath : "auto";
    entryPoint.replace("\"", "\\\"");

    QPair<QString, QString> classificationStr;
    switch(classification) {
    case SUCCESS:
        classificationStr = qMakePair<QString, QString>("succ", "Success");
        break;
    case FAILURE:
        classificationStr = qMakePair<QString, QString>("fail", "Failure");
        break;
    case UNKNOWN:// Fall-through
    default:
        classificationStr = qMakePair<QString, QString>("unk", "Unknown");
    }

    // Proper JSON support added in Qt5.0 unfortunately.
    // TODO: Now that we include the QJson lib, this part could be rewritten with that instead.
    QString json = "{\n";
    //json += QString("  \"url\": \"%1\",\n").arg(mUrl.toString());
    json += QString("  \"entrypoint\": \"%1\",\n").arg(entryPoint);
    json += QString("  \"explorationindex\": %1,\n").arg(mExplorationResult.target.explorationIndex);
    json += QString("  \"constraint\": \"%1\",\n").arg(mExplorationResult.constraintID);
    json += QString("  \"classification\": \"%1\",\n").arg(classificationStr.second);

    // TODO: Is this debug code still needed?
    // Debugging
    json += "  \"debugging\": [\n";

    int remainingInjections = mPreviousInjections.size(); // mPreviousInjections cannot change during this printing.
    foreach(QString var, mPreviousInjections.keys()) {
        InjectionValue inject = mPreviousInjections.value(var);

        QString value;
        switch(inject.getType()) {
        case QVariant::Bool:
            value = inject.getBool() ? "true" : "false";
            break;
        case QVariant::Int:
            value = QString::number(inject.getInt());
            break;
        case QVariant::String: // Fall-through
        default:
            value = "\"" + inject.getString() + "\"";
        }

        json += "    {\n";
        json += QString("      \"field\": \"%1\",\n").arg(var);
        json += QString("      \"value\": %1\n").arg(value);

        if(remainingInjections <= 1) {
            json += "    }\n";
        } else {
            json += "    },\n";
        }
        remainingInjections--;
    }

    json += "  ],\n";


    json += "  \"injection\": [\n";

    // Find the list of injected variables.
    QStringList varNames;
    foreach(FormFieldDescriptorConstPtr field, mFormFields) {
        QString var = field->getDomElement()->getId();
        if(mPreviousInjections.contains(var)) {
            varNames.append(var);
        }
    }

    // Write out the injection values. We need the list first so we can tell the last element.
    for(int i = 0; i < varNames.length(); i++) {
        InjectionValue inject = mPreviousInjections.value(varNames.at(i));

        QString value;
        switch(inject.getType()) {
        case QVariant::Bool:
            value = inject.getBool() ? "true" : "false";
            break;
        case QVariant::Int:
            value = QString::number(inject.getInt());
            break;
        case QVariant::String: // Fall-through
        default:
            value = "\"" + inject.getString() + "\"";
        }

        json += "    {\n";
        json += QString("      \"field\": \"%1\",\n").arg(varNames.at(i));
        json += QString("      \"value\": %1\n").arg(value);
        if(i == varNames.length() - 1) {
            json += "    }\n";
        } else {
            json += "    },\n";
        }
    }

    json += "  ]\n";

    json += "}\n";

    QString filename = QString("/tmp/injections/%1_%2.json").arg(QString::number(mExplorationResult.target.explorationIndex), classificationStr.first);

    createDir("/tmp", "injections");
    writeStringToFile(filename, json);
}


void ConcolicRuntime::done()
{
    reportStatistics();
    Runtime::done();
}


} // namespace artemis

