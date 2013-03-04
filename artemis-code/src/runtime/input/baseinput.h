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
#ifndef BASEINPUT_H
#define BASEINPUT_H

#include <QtWebKit/qwebexecutionlistener.h>
#include <QSharedPointer>

#include "runtime/browser/artemiswebpage.h"
#include "strategies/inputgenerator/event/eventparametergenerator.h"
#include "strategies/inputgenerator/form/forminputgenerator.h"
#include "strategies/inputgenerator/targets/targetgenerator.h"

namespace artemis
{

class BaseInput
{

public:
    virtual ~BaseInput() {}

    virtual void apply(ArtemisWebPagePtr page, QWebExecutionListener* webkitListener) const = 0;
    virtual QSharedPointer<const BaseInput> getPermutation(const QSharedPointer<const FormInputGenerator>& formInputGenerator,
                                                           const QSharedPointer<const EventParameterGenerator>& eventParameterGenerator,
                                                           TargetGenerator* targetGenerator,
                                                           QSharedPointer<const ExecutionResult> result) const = 0;

    virtual int hashCode() const = 0;
    virtual QString toString() const = 0;
};

}

#endif // BASEINPUT_H
