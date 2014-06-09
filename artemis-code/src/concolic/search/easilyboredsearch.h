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

#ifndef EASILYBOREDSEARCH_H
#define EASILYBOREDSEARCH_H

#include "concolic/executiontree/tracevisitor.h"
#include "randomaccesssearch.h"
#include "model/coverage/sourceinfo.h"

namespace artemis
{

/**
    Michael's easily bored search strategy.
 */
class EasilyBoredSearch : public RandomAccessSearch
{
public:
    EasilyBoredSearch(TraceNodePtr tree, uint searchBudget);

protected:
    QPair<bool, ExplorationDescriptor> nextTarget(QList<ExplorationDescriptor> possibleTargets);
    void newTraceAdded(TraceNodePtr node, int branch,TraceNodePtr suffix);
    void newUnsat(ExplorationDescriptor node);

private:
    QHash<QPair<QPair<uint, uint>, bool>, QPair<uint, uint> > counts;

    static QPair<QPair<uint, uint>, bool> getId(TraceBranchPtr node, bool branch);
    static QPair<QPair<uint, uint>, bool> getId(TraceBranch* node, bool branch);
    double getValue(ExplorationDescriptor target);

    /**
        Probability of choosing the best unexplored node.
     */
    static const double P = 0.9;

    class EasilyBoredVisitor : public TraceVisitor
    {
    public:
        EasilyBoredVisitor(EasilyBoredSearch* search);

    private:
        EasilyBoredSearch* search;

        void visit(TraceNode* node);
        void visit(TraceConcreteBranch* node);
        void visit(TraceSymbolicBranch* node);
        void visit(TraceConcreteSummarisation *node);
        void visit(TraceUnexplored* node);
        void visit(TraceAnnotation* node);
        void visit(TraceEnd* node);
    };
};

} //namespace artemis
#endif // EASILYBOREDSEARCH_H
