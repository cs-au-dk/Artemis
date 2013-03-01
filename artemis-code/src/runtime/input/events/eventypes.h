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
#ifndef EVENTYPES_H
#define EVENTYPES_H

#include <QString>

namespace artemis
{
enum EventType {KEY_EVENT,
                MOUSE_EVENT,
                BASE_EVENT,
                LOAD_EVENT,
                UNLOAD_EVENT,
                AJAX_READY_STATE_CHANGE,
                NON_INTERACTIVE_EVENT,
                TOUCH_EVENT,
                TIMER_EVENT,
                UNKNOWN_EVENT
               };

EventType getType(QString name);
bool isNonInteractive(QString name);
}

#endif // EVENTYPES_H
