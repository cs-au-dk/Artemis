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
#include "mouseeventparameters.h"
#include "artemisglobals.h"
#include "QString"
#include "util/randomutil.h"

namespace artemis
{

MouseEventParameters::MouseEventParameters(QObject* parent, QString type, bool canBubble, bool cancelable,
        int detail, int screenX, int screenY, int clientX, int clientY,
        bool ctrlKey, bool altKey, bool  shiftKey, bool  metaKey,
        int button)
    : EventParameters(parent)
{
    Q_ASSERT(!type.isEmpty());
    this->altKey = altKey;
    this->typeN = type;
    this->canBubble = canBubble;
    this->cancelable = cancelable;
    this->detail = detail;
    this->screenX = screenX;
    this->screenY = screenY;
    this->clientX = clientX;
    this->clientY = clientY;
    this->ctrlKey = ctrlKey;
    this->altKey = altKey;
    this->shiftKey = shiftKey;
    this->metaKey = metaKey;
    this->button = button;
}

/**
type
the string to set the event's type to. Possible types for mouse events include: click, mousedown, mouseup, mouseover, mousemove, mouseout.
canBubble
whether or not the event can bubble. Sets the value of event.bubbles.
cancelable
whether or not the event's default action can be prevented. Sets the value of event.cancelable.
view
the Event's AbstractView. You should pass the window object here. Sets the value of event.view.
detail
the Event's mouse click count. Sets the value of event.detail.
screenX
the Event's screen x coordinate. Sets the value of event.screenX.
screenY
the Event's screen y coordinate. Sets the value of event.screenY.
clientX
the Event's client x coordinate. Sets the value of event.clientX.
clientY
the Event's client y coordinate. Sets the value of event.clientY.
ctrlKey
whether or not control key was depressed during the Event. Sets the value of event.ctrlKey.
altKey
whether or not alt key was depressed during the Event. Sets the value of event.altKey.
shiftKey
whether or not shift key was depressed during the Event. Sets the value of event.shiftKey.
metaKey
whether or not meta key was depressed during the Event. Sets the value of event.metaKey.
button
the Event's mouse event.button.
relatedTarget
the Event's related EventTarget. Only used with some event types (e.g. mouseover and mouseout). In other cases, pass null.
  */
QString MouseEventParameters::jsString() const
{
    if (!cachedJsString.isEmpty()) {
        return cachedJsString;
    }

    QString randId = generateRandomJsId();
    QString res = "var " + randId + " = document.createEvent(\"MouseEvent\");";
    res = res + " " + randId + ".initMouseEvent(";
    res += quoteString(typeN) + ",";
    res += boolTostring(canBubble) + ",";
    res += boolTostring(cancelable) + ",";
    res += "window,";
    res += intTostring(detail) + ",";
    res += intTostring(screenX) + ",";
    res += intTostring(screenY) + ",";
    res += intTostring(clientX) + ",";
    res += intTostring(clientY) + ",";
    res += boolTostring(ctrlKey) + ",";
    res += boolTostring(altKey) + ",";
    res += boolTostring(shiftKey) + ",";
    res += boolTostring(metaKey) + ",";
    res += intTostring(button) + ",";
    res += "null);";

    res +=  "this.dispatchEvent(" + randId + ");";

    cachedJsString = res;
    return res;
}

EventType MouseEventParameters::type() const
{
    return MOUSE_EVENT;
}

}
