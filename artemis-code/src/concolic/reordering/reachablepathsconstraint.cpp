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

#include "reachablepathsconstraint.h"

namespace artemis
{

QSharedPointer<ReachablePathsOk> ReachablePathsOk::instance;
QSharedPointer<ReachablePathsAbort> ReachablePathsAbort::instance;

QSet<QString> ReachablePathsITE::freeVariableNames()
{
    ExpressionFreeVariableLister lister;
    condition->accept(&lister);
    QSet<QString> result = lister.getResult().keys().toSet();
    result.unite(thenConstraint->freeVariableNames());
    result.unite(elseConstraint->freeVariableNames());
    return result;
}

QSet<Symbolic::Expression*> ReachablePathsITE::getAllConditions()
{
    QSet<Symbolic::Expression*> result;
    result.insert(condition);
    result.unite(thenConstraint->getAllConditions());
    result.unite(elseConstraint->getAllConditions());
    return result;
}

QSet<QString> ReachablePathsDisjunction::freeVariableNames()
{
    QSet<QString> result;
    foreach (ReachablePathsConstraintPtr c, children) {
        result.unite(c->freeVariableNames());
    }
    return result;
}

QSet<Symbolic::Expression*> ReachablePathsDisjunction::getAllConditions()
{
    QSet<Symbolic::Expression*> result;
    foreach (ReachablePathsConstraintPtr c, children) {
        result.unite(c->getAllConditions());
    }
    return result;
}

QSharedPointer<ReachablePathsOk> ReachablePathsOk::getInstance()
{
    if (instance.isNull()) {
        instance = QSharedPointer<ReachablePathsOk>(new ReachablePathsOk());
    }
    return instance;
}

QSharedPointer<ReachablePathsAbort> ReachablePathsAbort::getInstance()
{
    if (instance.isNull()) {
        instance = QSharedPointer<ReachablePathsAbort>(new ReachablePathsAbort());
    }
    return instance;
}

} // namespace artemis

