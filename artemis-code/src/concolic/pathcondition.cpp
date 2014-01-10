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
    PathCondition* obj = new PathCondition();

    qDebug() << "GENERATE TRACE";

    if (!trace.isNull()) {
        trace->accept(obj);
    }

    return PathConditionPtr(obj);
}

void PathCondition::visit(TraceNode* node)
{
    // We should not fall back to this node, this indicates that we are missing a case
    qWarning("Warning: TraceNode catch-all reached, this should not happen");
    exit(1);
}

void PathCondition::visit(TraceSymbolicBranch* node)
{
    bool outcome = TraceVisitor::isImmediatelyUnexplored(node->getFalseBranch());
    mConditions.append(QPair<Symbolic::Expression*, bool>(node->getSymbolicCondition(), outcome));

    qDebug() << "ADD CONDITION " << outcome << node->getSymbolicCondition();

    if (outcome) {
        node->getTrueBranch()->accept(this);
    } else {
        node->getFalseBranch()->accept(this);
    }
}

void PathCondition::visit(TraceUnexplored* node)
{
    // We should not reach an unexplored node!
    qWarning("Warning: Unexplored node reached in traversal of execution trace");
    exit(1);
}

void PathCondition::visit(TraceAnnotation* node)
{
    node->next->accept(this);
}

void PathCondition::visit(TraceConcreteBranch *node)
{
    // Ignore the concrete branches

    if (TraceVisitor::isImmediatelyUnexplored(node->getFalseBranch())) {
        node->getTrueBranch()->accept(this);
    } else {
        node->getFalseBranch()->accept(this);
    }
}

void PathCondition::visit(TraceEnd* node)
{
    // Ignore the end node
}

void PathCondition::addCondition(Symbolic::Expression* condition, bool outcome)
{
    mConditions.append(qMakePair(condition, outcome));
}

const QPair<Symbolic::Expression*, bool> PathCondition::get(int index)
{
    return mConditions.at(index);
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
        mConditions.at(i).first->accept(&printer);

        sstrm << "PC[" << i << "]: " << printer.getResult() << std::endl;
    }

    return sstrm.str();
}

std::string PathCondition::toStatisticsValuesString(bool includeBranching)
{
    std::stringstream sstrm;

    for (int i = 0; i < mConditions.size(); i++) {
        ExpressionValuePrinter printer;
        mConditions.at(i).first->accept(&printer);

        if (includeBranching && !mConditions.at(i).second) {
            sstrm << "PC[" << i << "]: (" << printer.getResult() << " == false)" << std::endl;
        } else {
            sstrm << "PC[" << i << "]: " << printer.getResult() << std::endl;
        }
    }

    return sstrm.str();
}

QMap<QString, Symbolic::SourceIdentifierMethod> PathCondition::freeVariables()
{
    ExpressionFreeVariableLister lister;
    QMap<QString, Symbolic::SourceIdentifierMethod> vars;

    for (int i = 0; i < mConditions.size(); i++) {
        mConditions.at(i).first->accept(&lister);
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
    mConditions.last().second = !mConditions.last().second;
}

}
