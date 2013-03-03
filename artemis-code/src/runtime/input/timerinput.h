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
#ifndef TIMERINPUT_H
#define TIMERINPUT_H

#include "runtime/browser/timer.h"

#include "baseinput.h"

namespace artemis
{

class TimerInput: public BaseInput
{
public:
    TimerInput(QSharedPointer<const Timer> timer);

    void apply(ArtemisWebPage* page, QWebExecutionListener* webkitListener) const;
    QSharedPointer<const BaseInput> getPermutation(const QSharedPointer<const FormInputGenerator>& formInputGenerator,
                                                   const QSharedPointer<const EventParameterGenerator>& eventParameterGenerator,
                                                   TargetGenerator* targetGenerator,
                                                   QSharedPointer<const ExecutionResult> result) const;

    int hashCode() const;
    QString toString() const;

private:
    QSharedPointer<const Timer> mTimer;
};


}

#endif // TIMERINPUT_H
