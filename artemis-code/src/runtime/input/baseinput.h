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

#ifndef BASEINPUT_H
#define BASEINPUT_H

#include <QSharedPointer>

#include "runtime/browser/artemiswebpage.h"
#include "strategies/inputgenerator/event/eventparametergenerator.h"
#include "strategies/inputgenerator/form/forminputgenerator.h"
#include "strategies/inputgenerator/targets/targetgenerator.h"
#include "model/eventexecutionstatistics.h"
#include "model/stubeventexecutionstatistics.h"

namespace artemis
{

class BaseInput
{

public:

    BaseInput(){}
    BaseInput(EventExecutionStatistics* execStat): mExecStat(execStat){}

    virtual ~BaseInput() {}

    virtual void apply(ArtemisWebPagePtr page, QWebExecutionListener* webkitListener) const = 0;
    virtual QSharedPointer<const BaseInput> getPermutation(const FormInputGeneratorConstPtr& formInputGenerator,
                                                           const EventParameterGeneratorConstPtr& eventParameterGenerator,
                                                           const TargetGeneratorConstPtr& targetGenerator,
                                                           const ExecutionResultConstPtr& result) const = 0;

    virtual int hashCode() const = 0;
    virtual QString toString() const = 0;
protected:
    EventExecutionStatistics* mExecStat;
};

typedef QSharedPointer<const BaseInput> BaseInputConstPtr;

}

#endif // BASEINPUT_H
