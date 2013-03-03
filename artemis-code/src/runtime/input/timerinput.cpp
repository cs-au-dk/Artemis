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

#include <iostream>

#include "statistics/statsstorage.h"

#include "runtime/input/timerinput.h"

using namespace std;

namespace artemis
{

TimerInput::TimerInput(QSharedPointer<const Timer> timer)
{
    mTimer = timer;
}

void TimerInput::apply(ArtemisWebPage* page, QWebExecutionListener* webkitListener) const
{
    statistics()->accumulate("timers::fired", 1);
    webkitListener->timerFire(mTimer->getId());
}

QSharedPointer<const BaseInput> TimerInput::getPermutation(const QSharedPointer<const FormInputGenerator>&,
                                                           const QSharedPointer<const EventParameterGenerator>&,
                                                           TargetGenerator*,
                                                           QSharedPointer<const ExecutionResult>) const
{
    return QSharedPointer<const BaseInput>(this);
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
