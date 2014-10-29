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

#include <stdlib.h>
#include <sstream>
#include <QDebug>

#include "concolic/solver/expressionprinter.h"
#include "concolic/solver/expressionvalueprinter.h"
#include "concolic/solver/expressionfreevariablelister.h"

#include "util/loggingutil.h"

#include "pathcondition.h"

namespace artemis
{

PathCondition::PathCondition()
{

}

/**
 * Generate a path condition from the trace, this should not be an execution tree!
 */
PathConditionPtr PathCondition::createFromTrace(TraceNodePtr trace)
{
    BranchCheckingVisitor branchFinder;

    if (!trace.isNull()) {
        trace->accept(&branchFinder);
    }

    return createFromBranchList(branchFinder.mBranches);
}

QSharedPointer<PathCondition> PathCondition::createFromBranchList(PathBranchList branches)
{
    // In order to make a best-effort at searching for a new node, we simply ignore the conditions of branches which are known to be unsolvable.
    PathConditionPtr pc = PathConditionPtr(new PathCondition);
    foreach(PathBranch br, branches) {
        if(!br.first->isDifficult()) {
            pc->addCondition(br.first->getSymbolicCondition(), br.second, br.first);
        }
    }
    return pc;
}

void PathCondition::BranchCheckingVisitor::visit(TraceNode* node)
{
    // We should not fall back to this node, this indicates that we are missing a case
    qWarning("Warning: TraceNode catch-all reached, this should not happen");
    exit(1);
}

void PathCondition::BranchCheckingVisitor::visit(TraceSymbolicBranch* node)
{
    bool outcome = TraceVisitor::isImmediatelyUnexplored(node->getFalseBranch());
    mBranches.append(PathBranch(node, outcome));

    if (outcome) {
        node->getTrueBranch()->accept(this);
    } else {
        node->getFalseBranch()->accept(this);
    }
}

void PathCondition::BranchCheckingVisitor::visit(TraceUnexplored* node)
{
    // Ignore
}

void PathCondition::BranchCheckingVisitor::visit(TraceAnnotation* node)
{
    node->next->accept(this);
}

void PathCondition::BranchCheckingVisitor::visit(TraceConcreteSummarisation *node)
{
    // Ignore concrete summaries.
    foreach(TraceConcreteSummarisation::SingleExecution execution, node->executions) {
        execution.second->accept(this);
    }
}

void PathCondition::BranchCheckingVisitor::visit(TraceConcreteBranch *node)
{
    // Ignore the concrete branches
    node->getTrueBranch()->accept(this);
    node->getFalseBranch()->accept(this);
}

void PathCondition::BranchCheckingVisitor::visit(TraceEnd* node)
{
    // Ignore the end node
}

void PathCondition::addCondition(Symbolic::Expression* condition, bool outcome, TraceSymbolicBranch* branch)
{
    mConditions.append(qMakePair(qMakePair(condition, outcome), branch));
}

const QPair<Symbolic::Expression*, bool> PathCondition::get(int index)
{
    return mConditions.at(index).first;
}

TraceSymbolicBranch* PathCondition::getBranch(int index)
{
    return mConditions.at(index).second;
}

uint PathCondition::size()
{
    return mConditions.size();
}

std::string PathCondition::toStatisticsString()
{
    std::stringstream sstrm;

    for (int i = 0; i < mConditions.size(); i++) {
        ExpressionPrinter printer;
        mConditions.at(i).first.first->accept(&printer);

        sstrm << "PC[" << i << "]: " << printer.getResult() << std::endl;
    }

    return sstrm.str();
}

std::string PathCondition::toStatisticsValuesString(bool includeBranching)
{
    std::stringstream sstrm;

    for (int i = 0; i < mConditions.size(); i++) {
        ExpressionValuePrinter printer;
        mConditions.at(i).first.first->accept(&printer);

        if (includeBranching && !mConditions.at(i).first.second) {
            sstrm << "PC[" << i << "]: (" << printer.getResult() << " == false)" << std::endl;
        } else {
            sstrm << "PC[" << i << "]: " << printer.getResult() << std::endl;
        }

        TraceSymbolicBranch* branch = mConditions.at(i).second;
        sstrm << "  @ " << branch->getSource()->getUrl().toStdString() << ":" << branch->getSource()->getStartLine() << " line " << branch->getLinenumber() << std::endl;
    }

    return sstrm.str();
}

QMap<QString, Symbolic::SourceIdentifierMethod> PathCondition::freeVariables()
{
    ExpressionFreeVariableLister lister;
    QMap<QString, Symbolic::SourceIdentifierMethod> vars;

    for (int i = 0; i < mConditions.size(); i++) {
        mConditions.at(i).first.first->accept(&lister);
        // N.B. QMap::unite does not remove duplicates, so we can't use that.
        foreach(QString var, lister.getResult().keys()){
            vars.insert(var, lister.getResult().value(var));
        }
        lister.clear();
    }

    return vars;
}

void PathCondition::negateLastCondition()
{
    if (mConditions.size() > 0) {
        mConditions.last().first.second = !mConditions.last().first.second;
    }
}

}
