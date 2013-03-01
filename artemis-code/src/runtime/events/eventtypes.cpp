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
#include <QDebug>
#include "eventypes.h"

namespace artemis
{

EventType getType(QString name)
{
    Q_ASSERT(!name.isEmpty());

    if (name == "click"
        || name == "dblclick"
        || name == "mousedown"
        || name == "mouseup"
        || name == "mouseover"
        || name == "mousemove"
        || name == "mouseout")
        { return MOUSE_EVENT; }

    if (name == "keypress"
        || name == "keydown"
        || name == "keyup")
        { return KEY_EVENT; }

    if (name == "readystatechange")
        { return AJAX_READY_STATE_CHANGE; }

    if (name == "focus"
        || name == "blur"
        || name == "submit"
        || name == "reset"
        || name == "select"
        || name == "change"
        || name == "resize")
        { return BASE_EVENT; }

    if (name == "load"
        || name == "DOMContentLoaded"
        || name == "DOMFrameContentLoaded"
        || name == "pageshow")
        { return LOAD_EVENT; }

    if (name == "unload"
        || name == "pagehide"
        || name == "beforeunload")
        { return UNLOAD_EVENT; }

    if (name == "touchstart"
        || name == "touchend"
        || name == "touchmove")
        { return TOUCH_EVENT; }

    if (name == "abort"
        || name == "error")
        { return NON_INTERACTIVE_EVENT; }

    return UNKNOWN_EVENT;
}

bool isNonInteractive(QString name)
{
    EventType t = getType(name);
    return t == UNLOAD_EVENT || t == LOAD_EVENT || t == NON_INTERACTIVE_EVENT;
}
}
