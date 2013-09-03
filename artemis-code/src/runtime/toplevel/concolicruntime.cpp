/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "util/loggingutil.h"
#include "concolic/executiontree/tracemerger.h"
#include "concolic/solver/z3solver.h"

#include "concolicruntime.h"

namespace artemis
{


ConcolicRuntime::ConcolicRuntime(QObject* parent, const Options& options, const QUrl& url) :
    Runtime(parent, options, url)
{
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(postConcreteExecution(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));


}

void ConcolicRuntime::run(const QUrl& url)
{
    mUrl = url;

    mNextConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), url));

    mRunningToGetEntryPoints = true;
    mRunningWithInitialValues = false;

    mGraphOutputIndex = 1;
    mGraphOutputNameFormat = QString("tree-%1_%2.gv").arg(QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss"));

    preConcreteExecution();
}

void ConcolicRuntime::preConcreteExecution()
{
    if (mNextConfiguration.isNull()) {
        mWebkitExecutor->detach();
        done();
        return;
    }

    if(mRunningToGetEntryPoints){
        Log::debug("\n===== Entry-Point-Finding-Iteration =====");
    }else{
        if(mRunningWithInitialValues){
            Log::debug("\n=========== Initial-Iteration ===========");
        }else{
            Log::debug("\n============= New-Iteration =============");
        }
    }
    Log::debug("--------------- COVERAGE ----------------\n");
    Log::debug(mAppmodel->getCoverageListener()->toString().toStdString());

    mWebkitExecutor->executeSequence(mNextConfiguration); // calls the postConcreteExecution method as callback
}



// TODO: This method is a mess! It needs refactoring/reorganising ASAP.
void ConcolicRuntime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    /*
     * We can be in three possible states.
     *  1. mRunningToGetEntryPoints: A simple page load in which case we need to check for the entry points and choose one.
     *  2. mRunningWithInitialValues: The initial form submission. use this to seed the trace tree then choose a target.
     *  3. Neither: A normal run, where we add to the tree and choose a new target.
     */

    if(mRunningToGetEntryPoints){

        postInitialConcreteExecution(result); // Runs the next iteration itself.

    }else{
        // We already have an entry point.

        // Merge the new trace into the tree.
        // Sets up the search procedure and tree on the first run (when mRunningWithInitialValues is set).
        mergeTraceIntoTree();

        // Choose the next node to explore
        chooseNextTargetAndExplore();

    }
}






// Utility method to output the tree graph at each step.
void ConcolicRuntime::outputTreeGraph()
{
    // We want all the graphs from a certain run to have the same "base" name and an increasing index, so they can be easily grouped.
    QString name = mGraphOutputNameFormat.arg(mGraphOutputIndex);
    Log::debug(QString("CONCOLIC-INFO: Writing tree to file %1").arg(name).toStdString());
    mGraphOutputIndex++;

    mTraceDisplay.writeGraphFile(mSymbolicExecutionGraph, name, false);

    // TODO: Is there any way to have extra information added to the graph? e.g. the current target node.
}




// Given a FormInput, create an event sequence which will use that input and fire the entry point handler.
// Sets mNextConfiguration.
void ConcolicRuntime::setupNextConfiguration(QSharedPointer<FormInputCollection> formInput)
{
    // Create a suitable EventParameters object for this submission. (As in StaticEventParameterGenerator.)
    EventParametersConstPtr eventParameters = EventParametersConstPtr(new MouseEventParameters(mEntryPointEvent->getName(), true, true, 1, 0, 0, 0, 0, false, false, false, false, 0));

    // Create a suitable TargetDescriptor object for this submission.
    // TODO: No support for JQuery unless we use a JQueryTarget, JQueryListener (and TargetGenerator?).
    TargetDescriptorConstPtr targetDescriptor = TargetDescriptorConstPtr(new LegacyTarget(mEntryPointEvent));

    // Create a DomInput which will inject the empty FormInput and fire the entry point event.
    BaseInputConstPtr submitEvent = BaseInputConstPtr(new DomInput(mEntryPointEvent, formInput, eventParameters, targetDescriptor));
    // TODO:: Where should/are the eventParameters and targetDescriptor pointers cleaned up?

    // Create an input sequence consisting of just this event.
    QList<QSharedPointer<const BaseInput> > inputList;
    inputList.append(submitEvent);
    InputSequenceConstPtr inputSequence = InputSequenceConstPtr(new InputSequence(inputList));

    // Create an executableConfiguration from this niput sequence.
    mNextConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(inputSequence, mUrl));

    Log::debug("Next configuration is:");
    Log::debug(mNextConfiguration->toString().toStdString());
}


// Does the processing after the very first page load, to prepare for the testing.
void ConcolicRuntime::postInitialConcreteExecution(QSharedPointer<ExecutionResult> result)
{
    Log::debug("Analysing page entrypoints...");

    // Choose and save the entry point for use in future runs.
    EntryPointDetector detector(mWebkitExecutor->getPage());
    mEntryPointEvent = detector.choose(result);

    if(mEntryPointEvent){
        Log::debug(QString("Chose entry point %1").arg(mEntryPointEvent->toString()).toStdString());

        // Create an "empty" form input which will inject noting into the page.
        QList<FormInputPair > inputs;
        FormInputCollectionPtr formInput = FormInputCollectionPtr(new FormInputCollection(inputs));

        // Create the new event sequence and set mNextConfiguration.
        setupNextConfiguration(formInput);

        // Find the form fields on the page and save them.
        // TODO: We do this in the initial run so everything is stable, but at the cost of not being able to be at all dynamic (e.g. any form field not detected here will not be used correclty).
        mFormFields = result->getFormFields();

        // Print them
        Log::debug("Form fields found:");
        foreach(QSharedPointer<const FormFieldDescriptor> field, mFormFields){
            Log::debug(field->getDomElement()->toString().toStdString());
        }

        // On the next iteration, we will be running with initial values.
        mRunningToGetEntryPoints = false;
        mRunningWithInitialValues = true;

        // Execute this configuration.
        preConcreteExecution();

    }else{
        Log::debug("\n========== No Entry Points ==========");
        Log::debug("Could not find any suitable entry point for the analysis on this page. Exiting.");

        mWebkitExecutor->detach();
        done();
        return;
    }
}


// Creates the tree and sets up the search procedure and merges new traces into the tree.
void ConcolicRuntime::mergeTraceIntoTree()
{
    // First, we classify the trace which just ran.
    // This can  modify it to add the correct end marker to the trace.
    TraceNodePtr trace = mWebkitExecutor->getTraceBuilder()->trace();

    if(mTraceClassifier.classify(trace)){
        Log::debug("Recoreded trace was classified as a SUCCESS.");
    }else{
        Log::debug("Recoreded trace was classified as a FAILURE.");
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
    }else{
        // A normal run.
        // Merge trace with tracegraph
        mSymbolicExecutionGraph = TraceMerger::merge(trace, mSymbolicExecutionGraph);
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
                Log::debug(QString("%1 = %2").arg(var).arg(value.u.integer).toStdString());
                break;
            case Symbolic::BOOL:
                Log::debug(QString("%1 = %2").arg(var).arg(value.u.boolean ? "true" : "false").toStdString());
                break;
            case Symbolic::STRING:
                Log::debug(QString("%1 = %2").arg(var).arg(value.string.c_str()).toStdString());
                break;
            default:
                Log::info(QString("Unimplemented value type encountered for variable %1 (%2)").arg(var).arg(value.kind).toStdString());
                exit(1);
            }
        }else{
            Log::info(QString("Error: Could not find value for %1 in the solver's solution.").arg(var).toStdString());
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
            Log::info(QString("Error: Could not find value for %1 in the solver's solution.").arg(varName).toStdString());
            exit(1);
        }

        // Find the corresponding FormField by searching on the relevant attribute.
        QSharedPointer<const FormFieldDescriptor> varSourceField = findFormFieldForVariable(varName, freeVariables.value(varName));

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
            Log::info(QString("Unimplemented value type encountered for variable %1 (%2)").arg(varName).arg(value.kind).toStdString());
            exit(1);
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
        // Fetch the form field with this id
        foreach(QSharedPointer<const FormFieldDescriptor> field, mFormFields){
            if(field->getDomElement()->getName() == varBaseName){
                varSourceField = field;
                break;
            }
        }
        break;

    case Symbolic::ELEMENT_ID:
        // Fetch the form field with this id
        foreach(QSharedPointer<const FormFieldDescriptor> field, mFormFields){
            if(field->getDomElement()->getId() == varBaseName){
                varSourceField = field;
                break;
            }
        }
        break;

    case Symbolic::LEGACY:
        // TODO: The form fields without names or ids are just numbered, so I have no idea what to do here!
        Log::fatal("Identifying inputs by legacy numbering is not yet supported in the concolic runtime.");
        exit(1);
        break;

    default:
        Log::fatal("Unexpected identification method for form fields encountered.");
        exit(1);
        break;
    }

    // Check that we found a FormField.
    if(varSourceField.isNull()){
        Log::fatal(QString("Could not identify a form field for %1.").arg(varName).toStdString());
        exit(1);
    }

    return varSourceField;
}


// Generates a new solution from the path condition and runs it.
void ConcolicRuntime::exploreNextTarget()
{
    PathConditionPtr target = mSearchStrategy->getTargetPC();

    Log::debug("Target is: ");
    Log::debug(target->toStatisticsValuesString());

    // Get (and print) the list of free variables in the target PC.
    QMap<QString, Symbolic::SourceIdentifierMethod> freeVariables = target->freeVariables();
    QStringList varList = freeVariables.keys();

    Log::debug(QString("Variables we need to solve (%1):").arg(varList.length()).toStdString());
    Log::debug(varList.join(", ").toStdString());

    // Try to solve this PC to get some concrete input.
    Z3Solver solver;
    SolutionPtr solution = solver.solve(target);

    if(solution->isSolved()) {
        Log::debug("Solved the target Pc:");

        // Print this solution
        printSolution(solution, varList);


        QSharedPointer<FormInputCollection> formInput = createFormInput(freeVariables, solution);
        setupNextConfiguration(formInput);

        // Execute next iteration
        preConcreteExecution();

    }else{
        // TODO: Should try someting else/go concrete/...?
        Log::debug("Could not solve the constraint.");
        Log::debug("This case is not yet implemented!");
        Log::debug("Skipping this target!");

        // Skip this node and move on to the next.
        chooseNextTargetAndExplore();
    }
}


// Uses the search strategy to choose a new tsarget and then explore it.
void ConcolicRuntime::chooseNextTargetAndExplore()
{
    // Choose the next target.
    if(mSearchStrategy->chooseNextTarget()){

        // Explore this target. Runs the next execution itself.
        exploreNextTarget();

    }else{
        Log::debug("\n============= Finished DFS ==============");
        Log::debug("Finished serach of the tree (first pass at this depth).");

        if(mOptions.concolicTreeOutput == TREE_FINAL){
            outputTreeGraph();
        }

        mWebkitExecutor->detach();
        done();
        return;
    }
}



} // namespace artemis

