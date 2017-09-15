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

#include "symbolic/expression/expression.h"

namespace artemis
{

class ReachablePathsConstraint
{
public:
    virtual bool isAlwaysTerminating() = 0;
    virtual bool isAlwaysAborting() = 0;
};
typedef QSharedPointer<ReachablePathsConstraint> ReachablePathConstraintPtr;


class ReachablePathsITE : public ReachablePathsConstraint
{
public:
    Symbolic::Expression* condition;
    ReachablePathConstraintPtr thenConstraint;
    ReachablePathConstraintPtr elseConstraint;

    virtual bool isAlwaysTerminating() { return false; }
    virtual bool isAlwaysAborting() { return false; }
};

class ReachablePathsOk : public ReachablePathsConstraint
{
public:
    virtual bool isAlwaysTerminating() { return true; }
    virtual bool isAlwaysAborting() { return false; }
    static QSharedPointer<ReachablePathsOk> getInstance()
    {
        if (instance.isNull()) {
            instance = QSharedPointer(new ReachablePathsOk());
        }
        return instance;
    }
protected:
    ReachablePathsOk() {}
    static QSharedPointer<ReachablePathsOk> instance;
};

class ReachablePathsAbort : public ReachablePathsConstraint
{
public:
    virtual bool isAlwaysTerminating() { return false; }
    virtual bool isAlwaysAborting() { return true; }
    static QSharedPointer<ReachablePathsAbort> getInstance()
    {
        if (instance.isNull()) {
            instance = QSharedPointer(new ReachablePathsAbort());
        }
        return instance;
    }
protected:
    ReachablePathsAbort() {}
    static QSharedPointer<ReachablePathsAbort> instance;
};

} // namespace artemis
#endif // REACHABLEPATHSCONSTRAINT_H
