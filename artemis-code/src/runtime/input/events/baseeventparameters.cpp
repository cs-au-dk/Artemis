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
#include "baseeventparameters.h"
#include "eventypes.h"
#include "util/randomutil.h"

namespace artemis
{

BaseEventParameters::BaseEventParameters(QObject* parent, QString name, bool bubbles, bool cancelable)
    : EventParameters(parent)
{
    Q_ASSERT(!name.isEmpty());
    this->name = name;
    this->bubbles = bubbles;
    this->cancelable = cancelable;
}

QString BaseEventParameters::jsString() const
{
    if (!cachedJsString.isEmpty()) {
        return cachedJsString;
    }

    QString randId = generateRandomJsId();
    QString res = "var " + randId + " = document.createEvent(\"Event\");";
    res = res + " " + randId + ".initEvent(";
    res += quoteString(name) = ",";
    res += boolTostring(bubbles) + ",";
    res += boolTostring(cancelable) + ",);";

    res += "this.dispatchEvent(" + randId + ");";

    cachedJsString = res;
    return res;
}

EventType BaseEventParameters::type() const
{
    return BASE_EVENT;
}

}
