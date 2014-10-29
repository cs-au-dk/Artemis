/*
 * Copyright 2014 Aarhus University
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

#include "concolictarget.h"
#include "concolic/pathcondition.h"
#include "concolic/concolicanalysis.h"
#include "concolic/executiontree/tracedisplay.h"
#include "concolic/executiontree/tracedisplayoverview.h"

#include "concolictargetgenerator.h"

namespace artemis {

ConcolicTargetGenerator::ConcolicTargetGenerator(Options options, TraceBuilder* traceBuilder)
    : TargetGenerator()
    , mOptions(options)
    , mTraceBuilder(traceBuilder)
{
}

TargetDescriptorConstPtr ConcolicTargetGenerator::generateTarget(EventHandlerDescriptorConstPtr eventHandler) const
{
    // Create a context and save a reference in the returned target.
    // This reference can then be pulled out from oldTarget in permuteTarget below.
    ConcolicAnalysisPtr analysis(new ConcolicAnalysis(mOptions, ConcolicAnalysis::QUIET));
    ConcolicAnalysis::ExplorationHandle explorationTarget = ConcolicAnalysis::NO_EXPLORATION_TARGET;

    // TODO: Connect the ConcolicAnalysis signal for tree updates to something which can print out the tree?

    // No trace has been recorded yet, so we do not suggest any target values intelligently.
    // This method should do the naive solution and return a target == base handler (see legacy target impl.)

    return TargetDescriptorConstPtr(new ConcolicTarget(eventHandler, "", analysis, explorationTarget));
}

TargetDescriptorConstPtr ConcolicTargetGenerator::permuteTarget(EventHandlerDescriptorConstPtr eventHandler,
                                       TargetDescriptorConstPtr oldTarget,
                                       ExecutionResultConstPtr result) const
{
    // Notice that this function can be called multiple times with the same "oldTarget" and "result", because of how Artemis functions.
    // In this case the concolic analysis can return new explorations until there is nothing left to explore in the execution tree.

    // oldTarget should be of type ConcolicTargetDescriptor
    ConcolicTargetDescriptorConstPtr target = oldTarget.dynamicCast<const ConcolicTarget>();
    assert(!target.isNull());

    PathConditionPtr pc = PathCondition::createFromTrace(mTraceBuilder->trace());
    Log::debug("New PC found:");
    Log::debug(pc->toStatisticsValuesString(true));

    QString eventName = eventHandler->toString(); // TODO: better name would be useful...

    // The previous trace is guaranteed to be generated from oldTarget, so this should match our ConcolicTarrget.
    // Add the trace into the analysis, passing in the ExplorationHandle which lets the analysis know where this run was expected to exlpore.

    // We only start the symbolic session for the last event to be executed, and permuteTarget is only called for the
    // last event in an event sequence! -- we can assume that the event sequence reaching this event is constant.

    target->getAnalysis()->addTrace(mTraceBuilder->trace(), target->getExplorationTarget());

    // Now we can request suggestions of new targets to explore from the concolic analysis.
    ConcolicAnalysis::ExplorationResult exploration = target->getAnalysis()->nextExploration();

    if (!exploration.newExploration) {
        Log::debug("Could not find any new exploration");
        outputTree(target->getAnalysis()->getExecutionTree(), eventName, target->getAnalysis()->getExplorationIndex());
        return TargetDescriptorConstPtr(NULL); // TODO: is this the correct way to signal nothing to suggest?
    }

    Log::debug("PC solved:");
    Log::debug(pc->toStatisticsValuesString(true));

    Log::debug("Found solution for new target value:");
    printSolution(exploration.solution);

    outputTree(target->getAnalysis()->getExecutionTree(), eventName, target->getAnalysis()->getExplorationIndex());

    // The symbolic variable for the target will be TARGET_0.
    Symbolvalue newTarget = exploration.solution->findSymbol("SYM_TARGET_0");
    assert(newTarget.found); // TODO: should probably be a soft requirement once we are sure everything is working??
    QString targetXPath = QString::fromStdString(newTarget.string);

    // If a target is found, then return a ConcolicTarget with the context and a representation (xpath) of the target.
    // The runtime will call "get" on the target in the next iteration and use the xpath to find the real target.

    return TargetDescriptorConstPtr(new ConcolicTarget(eventHandler, targetXPath, target->getAnalysis(), exploration.target));

}


// TODO: Merge with ConcolicRuntime::printSolution and put somewhere accessible by both.
void ConcolicTargetGenerator::printSolution(const SolutionPtr solution) const
{
    QStringList symbols = solution->symbols();

    foreach (QString var, symbols) {
        Symbolvalue value = solution->findSymbol(var);
        assert(value.found);

        // TODO: Only object type should be seen here?
        switch (value.kind) {
        case Symbolic::INT:
            Log::debug(QString("    %1 = %2").arg(var).arg(value.u.integer).toStdString());
            break;
        case Symbolic::BOOL:
            Log::debug(QString("    %1 = %2").arg(var).arg(value.u.boolean ? "true" : "false").toStdString());
            break;
        case Symbolic::STRING:
            if (value.string.empty()) {
                Log::debug(QString("    %1 = \"\"").arg(var).toStdString());
            } else {
                Log::debug(QString("    %1 = \"%2\"").arg(var).arg(value.string.c_str()).toStdString());
            }
            break;
        case Symbolic::OBJECT:
            Log::debug(QString("    %1 -> %2").arg(var).arg(value.string.c_str()).toStdString());
            break;
        default:
            Log::fatal(QString("Unimplemented value type encountered for variable %1 (%2)").arg(var).arg(value.kind).toStdString());
            exit(1);
        }
    }
}

void ConcolicTargetGenerator::outputTree(TraceNodePtr tree, QString eventName, uint count) const
{
    // TODO: Make this stuff respect the concolic output options (e.g. whether to output them, whether to include the overview, whether to only keep the final one for each eventName, ...)
    if (mOptions.concolicTreeOutput == TREE_NONE) {
        return;
    }

    TraceDisplay display;
    TraceDisplayOverview display_min;

    QString date = QDateTime::currentDateTime().toString("yyyy-MM-dd-hh-mm-ss");
    QString filename = QString("event_%1_%2_%3.gv").arg(date, eventName).arg(count);
    QString filename_min = QString("event_%1_%2_%3_min.gv").arg(date, eventName).arg(count);

    display.writeGraphFile(tree, filename, false);
    display_min.writeGraphFile(tree, filename_min, false);
}


}
