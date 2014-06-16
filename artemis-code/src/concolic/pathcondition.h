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

#include <string>

#include <QList>
#include <QPair>
#include <QSharedPointer>

#include "JavaScriptCore/symbolic/expr.h"

#include "concolic/executiontree/tracenodes.h"
#include "concolic/executiontree/tracevisitor.h"

#ifndef PATHCONDITION_H
#define PATHCONDITION_H

namespace artemis
{

class PathCondition
{

public:
    PathCondition();

    static QSharedPointer<PathCondition> createFromTrace(TraceNodePtr endpoint);

    static QSharedPointer<PathCondition> createFromBranchList(QList<QPair<TraceSymbolicBranch*, bool> > branches);

    const QPair<Symbolic::Expression*, bool> get(int index);
    TraceSymbolicBranch* getBranch(int index);
    uint size();

    std::string toStatisticsString();
    std::string toStatisticsValuesString(bool includeBranching = false);
    QMap<QString, Symbolic::SourceIdentifierMethod> freeVariables();

    // Used to incrementally create a PC in the search procedure.
    void addCondition(Symbolic::Expression* condition, bool outcome, TraceSymbolicBranch* branch);

    void negateLastCondition();

private:
    QList<QPair<QPair<Symbolic::Expression*, bool>, TraceSymbolicBranch*> > mConditions;

    class BranchCheckingVisitor : public TraceVisitor
    {
    public:
        void visit(TraceNode* node);
        void visit(TraceConcreteBranch* node);
        void visit(TraceSymbolicBranch* node);
        void visit(TraceUnexplored* node);
        void visit(TraceAnnotation* node);
        void visit(TraceConcreteSummarisation* node);
        void visit(TraceEnd* node);

        QList<QPair<TraceSymbolicBranch*, bool> > mBranches;
    };
};

typedef QSharedPointer<PathCondition> PathConditionPtr;

typedef QPair<TraceSymbolicBranch*, bool> PathBranch;
typedef QList<QPair<TraceSymbolicBranch*, bool> > PathBranchList;

}

#endif // PATHCONDITION_H
