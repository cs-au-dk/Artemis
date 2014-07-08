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

#include "avoidunsatselector.h"
#include "randomaccesssearch.h"
#include "model/coverage/sourceinfo.h"
#include <QTime>
#include <assert.h>

namespace artemis
{


AvoidUnsatSelector::AvoidUnsatSelector()
{
    qsrand(QTime::currentTime().msec());
}

ExplorationDescriptor AvoidUnsatSelector::nextTarget(QList<ExplorationDescriptor> possibleTargets)
{
    ExplorationDescriptor bestTarget;
    if ((qrand() / (double) RAND_MAX) > P)
    {
        // choose a node randomly
        int index = qrand() % possibleTargets.length();
        bestTarget = possibleTargets.at(index);
    }
    else
    {
        // choose a node with the best value
        bestTarget = possibleTargets.at(0);
        double bestValue = this->getValue(bestTarget);
        for (int i = 1; i < possibleTargets.length(); i++)
        {
            ExplorationDescriptor currentTarget = possibleTargets.at(i);
            double currentValue = this->getValue(currentTarget);
            if (currentValue > bestValue)
            {
                bestTarget = currentTarget;
                bestValue = currentValue;
            }
        }
    }

    return bestTarget;
}

void AvoidUnsatSelector::newTraceAdded(TraceNodePtr node, int branch, TraceNodePtr suffix)
{
    // update count for current node
    TraceSymbolicBranchPtr branchNode = node.dynamicCast<TraceSymbolicBranch>();
    if (!branchNode.isNull())
    {
        QPair<QPair<uint, uint>, bool> id = getId(branchNode, branch == 1);
        this->counts[id].first++;
    }

    // process the new trace suffix
    suffix->accept(this);
}

void AvoidUnsatSelector::newUnsat(ExplorationDescriptor node)
{
    // update for a node that is unsatisfiable
    QPair<QPair<uint, uint>, bool> id = getId(node.branch, node.branchDirection);
    this->counts[id].second++;
}

QPair<QPair<uint, uint>, bool> AvoidUnsatSelector::getId(TraceBranchPtr node, bool branch)
{
    return getId(node.data(), branch);
}

QPair<QPair<uint, uint>, bool> AvoidUnsatSelector::getId(TraceBranch* node, bool branch)
{
    QPair<QPair<uint, uint>, bool> id;

    // id representing the source and the line number within the source
    id.first.first = SourceInfo::getId(node->getSource()->getUrl(), node->getSource()->getStartLine());

    // representing the offset
    id.first.second = node->getSourceOffset();

    // representing the branch
    id.second = branch;
    return id;
}

double AvoidUnsatSelector::getValue(ExplorationDescriptor node)
{
    QPair<QPair<uint, uint>, bool> id = AvoidUnsatSelector::getId(node.branch, node.branchDirection);
    QPair<uint, uint> counts = this->counts.value(id);

    if (counts.first == 0 && counts.second == 0)
    {
        return 1;
    }
    else
    {
        return counts.first / (double) (counts.first + counts.second);
    }
}

void AvoidUnsatSelector::visit(TraceNode* node)
{
    Log::fatal("Error: Reached a node of unknown type while searching the tree (EasilyBoredListener).");
    exit(1);
}

void AvoidUnsatSelector::visit(TraceConcreteBranch* node)
{
    node->getFalseBranch()->accept(this);
    node->getTrueBranch()->accept(this);
}

void AvoidUnsatSelector::visit(TraceSymbolicBranch* node)
{
    if (!isImmediatelyNotAttempted(node->getFalseBranch()))
    {
        // since the false branch was taken at this symbolic branch, update accordingly
        QPair<QPair<uint, uint>, bool> id = getId(node, false);
        this->counts[id].first++;

        // continue along the path
        node->getFalseBranch()->accept(this);
    }
    else
    {
        // the true branch was taken
        assert(!isImmediatelyNotAttempted(node->getTrueBranch()));

        // update accordingly
        QPair<QPair<uint, uint>, bool> id = getId(node, true);
        this->counts[id].first++;

        // continue along the path
        node->getTrueBranch()->accept(this);
    }
}

void AvoidUnsatSelector::visit(TraceConcreteSummarisation *node)
{
    foreach(TraceConcreteSummarisation::SingleExecution execution, node->executions)
    {
         execution.second->accept(this);
    }
}

void AvoidUnsatSelector::visit(TraceUnexplored* node)
{
    // ignore
}

void AvoidUnsatSelector::visit(TraceAnnotation* node)
{
    node->next->accept(this);
}

void AvoidUnsatSelector::visit(TraceEnd* node)
{
    // ignore
}

} // namespace artemis
