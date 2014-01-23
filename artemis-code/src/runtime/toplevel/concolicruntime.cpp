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
#include "concolic/executiontree/tracemerger.h"
#include "concolic/solver/z3solver.h"
#include "statistics/statsstorage.h"

#include "concolicruntime.h"

namespace artemis
{


ConcolicRuntime::ConcolicRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
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

    // The number of times we are willing to run the search procedure hoping to find some more nodes.
    // Note that if we know there are no unexplored nodes left we will stop anyway, so this is an upper limit.
    mSearchPasses = 3;
    mSearchPassesUnlimited = mOptions.concolicUnlimitedDepth;
    mSearchFoundTarget = false;
}

void ConcolicRuntime::run(const QUrl& url)
{
    mUrl = url;

    // We always run the first (no injection) load, to get the form fields and if necessary the entry-point.
    mRunningFirstLoad = true;
    mRunningWithInitialValues = false;

    mNextConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), url));

    mGraphOutputIndex = 1;
    mGraphOutputNameFormat = QString("tree-%1_%2%3.gv").arg(QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss"));

    std::ofstream constraintLog;
    constraintLog.open("/tmp/z3constraintlog", std::ofstream::out | std::ofstream::app);

    constraintLog << "================================================================================\n";
    constraintLog << "Begin concolic analysis of " << url.toString().toStdString() << " at " << QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss").toStdString() << "\n";
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

    mWebkitExecutor->executeSequence(mNextConfiguration); // calls the postConcreteExecution method as callback
}

void ConcolicRuntime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    /*
     * We can be in three possible states.
     *  1. mRunningFirstLoad: A simple page load in which case we need to check for the entry points and choose one, and save the fomr fields.
     *  2. mRunningWithInitialValues: The initial form submission. use this to seed the trace tree then choose a target.
     *  3. Neither: A normal run, where we add to the tree and choose a new target.
     */

    if(mRunningFirstLoad){

        postInitialConcreteExecution(result); // Runs the next iteration itself.

    }else{
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
    // We want all the graphs from a certain run to have the same "base" name and an increasing index, so they can be easily grouped.
    QString name = mGraphOutputNameFormat.arg("").arg(mGraphOutputIndex);
    QString name_min = mGraphOutputNameFormat.arg("min_").arg(mGraphOutputIndex);
    Log::debug(QString("CONCOLIC-INFO: Writing tree to file %1").arg(name).toStdString());
    mGraphOutputIndex++;

    mTraceDisplay.writeGraphFile(mSymbolicExecutionGraph, name, false);
    if(mOptions.concolicTreeOutputOverview){
        mTraceDisplayOverview.writeGraphFile(mSymbolicExecutionGraph, name_min, false);
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
        submitEvent = BaseInputConstPtr(new DomInput(mEntryPointEvent, formInput, eventParameters, targetDescriptor));
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

    // Print the form fields found on the page.
    Log::debug("Form fields found:");
    QStringList fieldNames;
    foreach(QSharedPointer<const FormFieldDescriptor> field, mFormFields){
        Log::debug(field->getDomElement()->toString().toStdString());
        fieldNames.append(field->getDomElement()->toString());
    }
    Log::info(QString("  Form fields: %1").arg(fieldNames.join(", ")).toStdString());

    // Create an "empty" form input which will inject noting into the page.
    QList<FormInputPair > inputs;
    FormInputCollectionPtr formInput = FormInputCollectionPtr(new FormInputCollection(inputs));

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
    if(mRunningWithInitialValues){
        // After the very first run we need to set up the tree & search procedure.
        // We can't just begin with an empty tree and merge every trace in, as the search procedure needs a
        // pointer to the tree, which will be replaced in that case.
        // If this is a problem, we could just introduce a header node for trees.
        mSymbolicExecutionGraph = trace;
        mSearchStrategy = DepthFirstSearchPtr(new DepthFirstSearch(mSymbolicExecutionGraph));
        mRunningWithInitialValues = false;

        statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
    }else{
        // A normal run.
        // Merge trace with tracegraph
        mSymbolicExecutionGraph = TraceMerger::merge(trace, mSymbolicExecutionGraph);

        // Check if we actually explored the intended target.
        if(mSearchStrategy->overUnexploredNode()){
            mSearchStrategy->markNodeMissed();
            Log::info("  Recorded trace did not take the expected path.");
        }else{
            statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);
        }
    }

    // Dump the current state of the tree to a file.
    if(mOptions.concolicTreeOutput == TREE_ALL){
        outputTreeGraph();
    }
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
                    Log::info(QString("    %1 = %2").arg(var).arg(value.string.c_str()).toStdString());
                }
                break;
            default:
                Log::fatal(QString("Unimplemented value type encountered for variable %1 (%2)").arg(var).arg(value.kind).toStdString());
                exit(1);
            }
        }else{
            Log::fatal(QString("Error: Could not find value for %1 in the solver's solution.").arg(var).toStdString());
            exit(1);
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
            statistics()->accumulate("Concolic::FailedInjections", 1);
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
        case Symbolic::INT:
            inputs.append(FormInputPair(varSourceField, QString::number(value.u.integer)));
            Log::debug(QString("Injecting %1 into %2").arg(QString::number(value.u.integer)).arg(varName).toStdString());
            break;
        case Symbolic::BOOL:
            inputs.append(FormInputPair(varSourceField, QString(value.u.boolean ? "true" : "false"))); // TODO: How to represent booleans here?
            Log::debug(QString("Injecting %1 into %2").arg(value.u.boolean ? "true" : "false").arg(varName).toStdString());
            break;
        case Symbolic::STRING:
            inputs.append(FormInputPair(varSourceField, QString(value.string.c_str())));
            Log::debug(QString("Injecting %1 into %2").arg(QString(value.string.c_str())).arg(varName).toStdString());
            break;
        default:
            Log::error(QString("Unimplemented value type encountered for variable %1 (%2)").arg(varName).arg(value.kind).toStdString());
            statistics()->accumulate("Concolic::FailedInjections", 1);
            continue;
        }

    }


    // Set up a new configuration which tests this input.
    return QSharedPointer<FormInputCollection>(new FormInputCollection(inputs));
}


// Given a symbolic variable, find the corresponding form field on the page.
QSharedPointer<const FormFieldDescriptor> ConcolicRuntime::findFormFieldForVariable(QString varName, Symbolic::SourceIdentifierMethod varSourceIdentifierMethod)
{
    QSharedPointer<const FormFieldDescriptor> varSourceField;

    // Variable names are of the form SYM_IN_<name>, and we will need to use <name> directly when searching the ids and names of the form fields.
    QString varBaseName = varName;
    varBaseName.replace("SYM_IN_", "");

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
        statistics()->accumulate("Concolic::FailedInjections", 1);
        return varSourceField; // Returning null to signify error.
    }

    // Check that we found a FormField.
    if(varSourceField.isNull()){
        Log::error(QString("Error: Could not identify a form field for %1.").arg(varName).toStdString());
        statistics()->accumulate("Concolic::FailedInjections", 1);
        return varSourceField; // Returning null to signify error.
    }

    return varSourceField;
}


// Generates a new solution from the path condition and runs it.
void ConcolicRuntime::exploreNextTarget()
{
    PathConditionPtr target = mSearchStrategy->getTargetPC();

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
    Z3Solver solver;
    SolutionPtr solution = solver.solve(target);

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
            mSearchStrategy->markNodeUnsolvable();
            Log::info("  Could not solve constraint:");
            Log::info(QString("    %1").arg(solution->getUnsolvableReason()).toStdString());
        }
        Log::debug("Skipping this target!");

        // Dump the current state of the tree to a file.
        if(mOptions.concolicTreeOutput == TREE_ALL){
            outputTreeGraph();
        }

        // Skip this node and move on to the next.
        chooseNextTargetAndExplore();
    }
}


// Uses the search strategy to choose a new target and then explore it.
void ConcolicRuntime::chooseNextTargetAndExplore()
{
    // Choose the next target.
    if(mSearchStrategy->chooseNextTarget()){
        mSearchFoundTarget = true;

        // Explore this target. Runs the next execution itself.
        exploreNextTarget();

    }else if (mSearchFoundTarget && (mSearchPassesUnlimited || mSearchPasses > 1)){
        mSearchFoundTarget = false;
        if(!mSearchPassesUnlimited){
            mSearchPasses--;
        }

        Log::debug("\n============= Finished DFS ==============");
        Log::info("Finished this pass of the tree. Increasing depth limit and restarting.");

        mSearchStrategy->setDepthLimit(mSearchStrategy->getDepthLimit() + 5);
        mSearchStrategy->restartSearch();
        chooseNextTargetAndExplore();

    }else{
        Log::debug("\n============= Finished DFS ==============");
        Log::info("Finished serach of the tree.");

        if(mOptions.concolicTreeOutput == TREE_FINAL){
            // "Fake" the counter for graph output, as this will be the only one we create.
            mGraphOutputIndex = mNumIterations;
            outputTreeGraph();
        }

        mWebkitExecutor->detach();
        done();
        return;
    }
}


void ConcolicRuntime::done()
{
    statistics()->accumulate("Concolic::Iterations", mNumIterations);
    Runtime::done();
}


} // namespace artemis

