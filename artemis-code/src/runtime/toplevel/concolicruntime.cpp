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

        Log::debug("Analysing page entrypoints...");
        EntryPointDetector detector(mWebkitExecutor->getPage());
        // Choose and save the entry point for use in future runs.
        mEntryPointEvent = detector.choose(result);
        if(mEntryPointEvent){
            Log::debug(QString("Chose entry point %1").arg(mEntryPointEvent->toString()).toStdString());

            // Create an "empty" form input which will inject noting into the page.
            QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> > inputs;
            QSharedPointer<FormInput> formInput = QSharedPointer<FormInput>(new FormInput(inputs));

            // Create a suitable EventParameters object for this submission. (As in StaticEventParameterGenerator.)
            EventParameters* eventParameters = new MouseEventParameters(NULL, mEntryPointEvent->name(), true, true, 1, 0, 0, 0, 0, false, false, false, false, 0);

            // Create a suitable TargetDescriptor object for this submission.
            // TODO: No support for JQuery unless we use a JQueryTarget, JQueryListener (and TargetGenerator?).
            TargetDescriptor* targetDescriptor = new LegacyTarget(NULL, mEntryPointEvent);

            // Create a DomInput which will inject the empty FormInput and fire the entry point event.
            QSharedPointer<const BaseInput> submitEvent = QSharedPointer<const BaseInput>(new DomInput(mEntryPointEvent, formInput, eventParameters, targetDescriptor));
            // TODO:: Where should/are the eventParameters and targetDescriptor pointers cleaned up?

            // Create an input sequence consisting of just this event.
            QList<QSharedPointer<const BaseInput> > inputList;
            inputList.append(submitEvent);
            InputSequenceConstPtr inputSequence = InputSequenceConstPtr(new InputSequence(inputList));

            // Create an executableConfiguration from this niput sequence.
            mNextConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(inputSequence, mUrl));

            Log::debug("Next configuration is:");
            Log::debug(mNextConfiguration->toString().toStdString());

            // Move to state 2 and execute this initial configuration.
            mRunningToGetEntryPoints = false;
            mRunningWithInitialValues = true;
            preConcreteExecution();

        }else{
            Log::debug("\n========== No Entry Points ==========");
            Log::debug("Could not find any suitable entry point for the analysis on this page. Ending.");

            mWebkitExecutor->detach();
            done();
            return;
        }

    }else{
        // We already have an entry point.

        if(mRunningWithInitialValues){
            // After the very first run we need to set up the tree & search procedure.
            mSymbolicExecutionGraph = mWebkitExecutor->getTraceBuilder()->trace();
            mSearchStrategy = DepthFirstSearchPtr(new DepthFirstSearch(mSymbolicExecutionGraph));
            Log::debug("Created trace tree from initial trace.");
        }else{
            // A normal run.
            // Merge trace with tracegraph
            mSymbolicExecutionGraph = TraceMerger::merge(mWebkitExecutor->getTraceBuilder()->trace(), mSymbolicExecutionGraph);
        }

        // Print the trace tree.
        // TODO: don't do this, it will be a mess on big trees!
        Log::info("The trace tree: ");
        TerminalTracePrinter termPrinter;
        termPrinter.printTraceTree(mSymbolicExecutionGraph);

        // Dump the current state of the tree to a file.
        //outputTreeGraph(); // TODO: re-enable this once I am actually running some sensible iterations!

        // Choose the next node to explore
        if(mSearchStrategy->chooseNextTarget()){
            PathConditionPtr target = mSearchStrategy->getTargetPC();

            Log::debug("Target is: ");
            Log::debug(target->toStatisticsValuesString());

            // Get (and print) the list of free variables in the target PC.
            QStringList varList(target->freeVariables().toList());
            Log::debug(QString("Variables we need to solve (%1):").arg(varList.length()).toStdString());
            Log::debug(varList.join(", ").toStdString());

            // Try to solve this PC to get some concrete input.
            SolutionPtr solution = Solver::solve(target);

            if(!solution->isSolved()){
                // TODO: Should try someting else/go concrete/...?
                Log::debug("\n============= Finished DFS ==============");
                Log::debug("Could not solve the constraint.");
                Log::debug("This case is not yet implemented!");

                mWebkitExecutor->detach();
                done();
                return;

            }else{
                Log::debug("Solved the target Pc:");
                // TODO: can we print this solution?

                // Translate the solution into a concrete input.
                // TODO

                // Set up a new configuration which tests this input.
                // TODO

                Log::info("TODO *************************************");
                exit(1);

                // TODO: not sure what this is. It was in the "blank" version of this method left by Casper, so I should look into it.
                mNextConfiguration.clear();

                // Execute next iteration
                preConcreteExecution();
            }

        }else{
            Log::debug("\n============= Finished DFS ==============");
            Log::debug("Finished serach of the tree (first pass at this depth).");

            mWebkitExecutor->detach();
            done();
            return;
        }

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

} // namespace artemis

