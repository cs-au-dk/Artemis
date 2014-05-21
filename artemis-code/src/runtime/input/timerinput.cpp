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

#include <iostream>

#include <QWebExecutionListener>

#include "statistics/statsstorage.h"

#include "runtime/input/timerinput.h"

using namespace std;

namespace artemis
{

TimerInput::TimerInput(QSharedPointer<const Timer> timer)
{
    mTimer = timer;
}

void TimerInput::apply(ArtemisWebPagePtr, QWebExecutionListener* webkitListener) const
{
    Statistics::statistics()->accumulate("timers::fired", 1); webkitListener->timerFire(mTimer->getId());
}

BaseInputConstPtr TimerInput::getPermutation(const FormInputGeneratorConstPtr& formInputGenerator,
                                             const EventParameterGeneratorConstPtr& eventParameterGenerator,
                                             const TargetGeneratorConstPtr& targetGenerator,
                                             const ExecutionResultConstPtr& result) const
{
    return QSharedPointer<const BaseInput>(new TimerInput(this->mTimer));
}

int TimerInput::hashCode() const
{
    return 31 * mTimer->getId();
}

QString TimerInput::toString() const
{
    return QString("TimerInput");
}

}
