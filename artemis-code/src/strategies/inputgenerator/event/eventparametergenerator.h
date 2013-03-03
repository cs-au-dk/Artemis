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
#ifndef EVENTPARAMETERGENERATOR_H
#define EVENTPARAMETERGENERATOR_H

#include <QObject>
#include <QSet>

#include "runtime/input/events/eventparameters.h"
#include "runtime/input/events/eventhandlerdescriptor.h"
#include "runtime/input/forms/formfield.h"
#include "runtime/input/forms/forminput.h"

namespace artemis
{

class EventParameterGenerator
{

public:
    EventParameterGenerator() {}
    virtual ~EventParameterGenerator() {}

    virtual EventParameters* generateEventParameters(QObject* parent, const EventHandlerDescriptor* eventHandler) const = 0;
};

}

#endif // EVENTPARAMETERGENERATOR_H
