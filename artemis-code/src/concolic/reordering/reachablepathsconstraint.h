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

#ifndef REACHABLEPATHSCONSTRAINT_H
#define REACHABLEPATHSCONSTRAINT_H

#include <QSharedPointer>
#include <QSet>
#include <QPair>
#include <QString>

#include "symbolic/expression/expression.h"
#include "concolic/solver/expressionfreevariablelister.h"


namespace artemis
{

class ReachablePathsConstraint
{
public:
    virtual bool isAlwaysTerminating() = 0;
    virtual bool isAlwaysAborting() = 0;

    virtual QSet<QString> freeVariableNames() = 0;
    virtual QSet<Symbolic::Expression*> getAllConditions() = 0;

    virtual ~ReachablePathsConstraint() {}
};
typedef QSharedPointer<ReachablePathsConstraint> ReachablePathsConstraintPtr;


class ReachablePathsITE : public ReachablePathsConstraint
{
public:
    ReachablePathsITE() {}

    Symbolic::Expression* condition;
    ReachablePathsConstraintPtr thenConstraint;
    ReachablePathsConstraintPtr elseConstraint;

    virtual bool isAlwaysTerminating() { return false; }
    virtual bool isAlwaysAborting() { return false; }
    virtual QSet<QString> freeVariableNames();
    virtual QSet<Symbolic::Expression*> getAllConditions();
};

class ReachablePathsDisjunction : public ReachablePathsConstraint
{
public:
    ReachablePathsDisjunction() {}

    QList<ReachablePathsConstraintPtr> children;

    virtual bool isAlwaysTerminating() { return false; }
    virtual bool isAlwaysAborting() { return false; }
    virtual QSet<QString> freeVariableNames();
    virtual QSet<Symbolic::Expression*> getAllConditions();
};

class ReachablePathsOk : public ReachablePathsConstraint
{
public:
    virtual bool isAlwaysTerminating() { return true; }
    virtual bool isAlwaysAborting() { return false; }
    virtual QSet<QString> freeVariableNames() { return QSet<QString>(); }
    virtual QSet<Symbolic::Expression*> getAllConditions() { return QSet<Symbolic::Expression*>(); }

    static QSharedPointer<ReachablePathsOk> getInstance();
protected:
    ReachablePathsOk() {}
    static QSharedPointer<ReachablePathsOk> instance;
};

class ReachablePathsAbort : public ReachablePathsConstraint
{
public:
    virtual bool isAlwaysTerminating() { return false; }
    virtual bool isAlwaysAborting() { return true; }
    virtual QSet<QString> freeVariableNames() { return QSet<QString>(); }
    virtual QSet<Symbolic::Expression*> getAllConditions() { return QSet<Symbolic::Expression*>(); }

    static QSharedPointer<ReachablePathsAbort> getInstance();
protected:
    ReachablePathsAbort() {}
    static QSharedPointer<ReachablePathsAbort> instance;
};

typedef QPair<QPair<QString, uint>, ReachablePathsConstraintPtr> NamedReachablePathsConstraint;
typedef QSet<NamedReachablePathsConstraint> ReachablePathsConstraintSet;

} // namespace artemis
#endif // REACHABLEPATHSCONSTRAINT_H
