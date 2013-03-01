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
#ifndef BASEEVENTPARAMETERS_H
#define BASEEVENTPARAMETERS_H

#include "artemisglobals.h"
#include "eventparameters.h"

namespace artemis
{

class BaseEventParameters : public EventParameters
{
public:
    BaseEventParameters(QObject* parent, QString type, bool bubbles, bool cancelable);

    QString jsString() const ;
    EventType type() const;

private:
    QString name;
    bool cancelable;
    bool bubbles;
    mutable QString cachedJsString;

};

}

#endif // BASEEVENTPARAMETERS_H
