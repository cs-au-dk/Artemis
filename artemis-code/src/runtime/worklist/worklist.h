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

#ifndef WORKLIST_H
#define WORKLIST_H

#include <QString>
#include <QSharedPointer>

#include "runtime/executableconfiguration.h"
#include "runtime/appmodel.h"

namespace artemis
{

class WorkList
{

public:
    WorkList() {}
    virtual ~WorkList() {}

    virtual void add(ExecutableConfigurationConstPtr configuration, AppModelConstPtr appmodel) = 0;
    virtual ExecutableConfigurationConstPtr remove() = 0;

    virtual void reprioritize(AppModelConstPtr appmodel) = 0;

    virtual int size() = 0;
    virtual bool empty() = 0;

    virtual QString toString() const = 0;
};

typedef QSharedPointer<WorkList> WorkListPtr;
typedef QSharedPointer<const WorkList> WorkListConstPtr;

}

#endif // WORKLIST_H
