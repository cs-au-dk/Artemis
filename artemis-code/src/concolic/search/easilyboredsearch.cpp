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

#include "easilyboredsearch.h"

#include <QTime>
#include <assert.h>

namespace artemis
{


EasilyBoredSearch::EasilyBoredSearch(TraceNodePtr tree, uint searchBudget) : RandomAccessSearch(tree, searchBudget)
{
    qsrand(QTime::currentTime().msec());
}

/**
    Selects a node from the given list of unexplored nodes.
    The node is chosen in such a way that the likelihood of encountering
    an unsatisfiable constraint is minimized.

    @param possibleTargets a list of unexplored nodes.
    @pre. possibleTargets is a nonempty list.
    @return a pair consisting of the Boolean true and an unexplored node.
 */
QPair<bool, RandomAccessSearch::ExplorationDescriptor> EasilyBoredSearch::nextTarget(QList<RandomAccessSearch::ExplorationDescriptor> possibleTargets)
{
    ExplorationDescriptor bestTarget;
    if ((qrand() / (double) RAND_MAX) > P)
    {
        int index = qrand() % possibleTargets.length();
        bestTarget = possibleTargets.at(index);
    }
    else
    {
        bestTarget = possibleTargets.at(0);
        double bestValue = getValue(bestTarget);
        for (int i = 1; i < possibleTargets.length(); i++)
        {
            ExplorationDescriptor currentTarget = possibleTargets.at(i);
            double currentValue = getValue(currentTarget);
            if (currentValue > bestValue)
            {
                bestTarget = currentTarget;
                bestValue = currentValue;
            }
        }
    }

    return QPair<bool, RandomAccessSearch::ExplorationDescriptor>(true, bestTarget);
}

/**
    Updates the data, given a node and one of its branches.

    @param node a node.
    @param branch a branch of the node.
    @param suffix redundant.
 */
void EasilyBoredSearch::newTraceAdded(TraceNodePtr node, int branch, TraceNodePtr suffix)
{
    // Update count for current node.
    TraceSymbolicBranchPtr branchNode = node.dynamicCast<TraceSymbolicBranch>();
    if(!branchNode.isNull()) {
        QPair<QPair<uint, uint>, bool> id = getId(branchNode, branch == 1);
        this->counts[id].first++;
    }

    // Process the new trace suffix
    EasilyBoredVisitor visitor(this);
    suffix->accept(&visitor);
}

EasilyBoredSearch::EasilyBoredVisitor::EasilyBoredVisitor(EasilyBoredSearch* search) :
    search(search)
{
}

void EasilyBoredSearch::EasilyBoredVisitor::visit(TraceNode* node)
{
    Log::fatal("Error: Reached a node of unknown type while searching the tree (EasilyBoredSearch).");
    exit(1);
}

void EasilyBoredSearch::EasilyBoredVisitor::visit(TraceConcreteBranch* node)
{
    node->getFalseBranch()->accept(this);
    node->getTrueBranch()->accept(this);
}

void EasilyBoredSearch::EasilyBoredVisitor::visit(TraceSymbolicBranch* node)
{
    if(!isImmediatelyNotAttempted(node->getFalseBranch())) {
        QPair<QPair<uint, uint>, bool> id = getId(node, false);
        search->counts[id].first++;

        node->getFalseBranch()->accept(this);

    } else {
        assert(!isImmediatelyNotAttempted(node->getTrueBranch()));

        QPair<QPair<uint, uint>, bool> id = getId(node, true);
        search->counts[id].first++;

        node->getTrueBranch()->accept(this);
    }
}

void EasilyBoredSearch::EasilyBoredVisitor::visit(TraceConcreteSummarisation *node)
{
    foreach(TraceConcreteSummarisation::SingleExecution execution, node->executions) {
         execution.second->accept(this);
    }
}

void EasilyBoredSearch::EasilyBoredVisitor::visit(TraceUnexplored* node)
{
    // ignore
}

void EasilyBoredSearch::EasilyBoredVisitor::visit(TraceAnnotation* node)
{
    node->next->accept(this);
}

void EasilyBoredSearch::EasilyBoredVisitor::visit(TraceEnd* node)
{
    // ignore
}

/**
    Updates the data to reflect that the given node and branch turned out to be unsatisfiable.

    @param node a node (and its branch).
 */
void EasilyBoredSearch::newUnsat(ExplorationDescriptor node)
{
    QPair<QPair<uint, uint>, bool> id = getId(node.branch, node.branchDirection);
    this->counts[id].second++;
}

/**
    Returns the id of the given node and branch.

    @param node a node.
    @param branch a branch of the node.
    @return the id of the given node and branch.
 */
QPair<QPair<uint, uint>, bool> EasilyBoredSearch::getId(TraceBranchPtr node, bool branch)
{
    return getId(node.data(), branch);
}

QPair<QPair<uint, uint>, bool> EasilyBoredSearch::getId(TraceBranch* node, bool branch)
{
    QPair<QPair<uint, uint>, bool> id;
    id.first.first = SourceInfo::getId(node->getSource()->getUrl(), node->getSource()->getStartLine());
    id.first.second = node->getSourceOffset();
    id.second = branch;
    return id;
}

/**
    Returns the value of the given node and branch.

    @param node a node (and its branch).
    @return the value of the given node and branch.
 */
double EasilyBoredSearch::getValue(RandomAccessSearch::ExplorationDescriptor node)
{
    QPair<QPair<uint, uint>, bool> id = getId(node.branch, node.branchDirection);
    QPair<uint, uint> counts = this->counts.value(id);

    if(counts.first == 0 && counts.second == 0) {
        return 1;
    } else {
        return counts.first / (double) (counts.first + counts.second);
    }
}


} //namespace artemis
