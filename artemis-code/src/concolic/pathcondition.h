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

class PathCondition : public TraceVisitor
{

public:
    PathCondition();

    static QSharedPointer<PathCondition> createFromTrace(TraceNodePtr endpoint);

    const QPair<Symbolic::Expression*, bool> get(int index);
    uint size();

    std::string toStatisticsString();
    std::string toStatisticsValuesString();

    void visit(TraceNode* node);
    void visit(TraceConcreteBranch* node);
    void visit(TraceSymbolicBranch* node);
    void visit(TraceUnexplored* node);
    void visit(TraceAnnotation* node);
    void visit(TraceEnd* node);

    // Used to incrementally create a PC in the search procedure.
    void addCondition(Symbolic::Expression* condition, bool outcome);

private:
    QList<QPair<Symbolic::Expression*, bool> > mConditions;
};

typedef QSharedPointer<PathCondition> PathConditionPtr;

}

#endif // PATHCONDITION_H
