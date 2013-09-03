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

#include <assert.h>
#include <util/randomutil.h>

#include <QSet>
#include <QList>

#include "runtime/input/events/baseeventparameters.h"
#include "runtime/input/events/keyboardeventparameters.h"
#include "runtime/input/events/mouseeventparameters.h"
#include "runtime/input/events/toucheventparameters.h"
#include "runtime/input/events/unknowneventparameters.h"

#include "staticeventparametergenerator.h"

namespace artemis
{

StaticEventParameterGenerator::StaticEventParameterGenerator() : EventParameterGenerator()
{
}

EventParametersConstPtr StaticEventParameterGenerator::generateEventParameters(EventHandlerDescriptorConstPtr eventHandler) const
{

    switch (eventHandler->getEventType()) {

    case BASE_EVENT:
        return EventParametersConstPtr(new BaseEventParameters(eventHandler->getName(), true, true));
        break;

    case MOUSE_EVENT:
        return EventParametersConstPtr(new MouseEventParameters(eventHandler->getName(),
                                        true,
                                        true,
                                        1,
                                        0,
                                        0,
                                        0,
                                        0,
                                        false,
                                        false,
                                        false,
                                        false,
                                        0));
        break;

    case KEY_EVENT:
        return EventParametersConstPtr(new KeyboardEventParameters(eventHandler->getName(),
                                           true,
                                           true,
                                           QString("a"),
                                           0,
                                           false,
                                           false,
                                           false,
                                           false,
                                           false));
        break;
    case TOUCH_EVENT:
        return EventParametersConstPtr(new TouchEventParameters());

    default:
        qDebug() << "Unknown event type!";
        return EventParametersConstPtr(new UnknownEventParameters());
    }
}

}
