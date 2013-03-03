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
#ifndef KEYBOARDEVENTPARAMETERS_H
#define KEYBOARDEVENTPARAMETERS_H

#include "eventparameters.h"
#include <QString>

namespace artemis
{

class KeyboardEventParameters : public EventParameters
{
public:

    KeyboardEventParameters(QObject* parent, QString eventType, bool canBubble, bool cancelable,
                            QString keyIdentifier,  unsigned int keyLocation,
                            bool ctrlKey, bool altKey, bool shiftKey, bool metaKey, bool altGraphKey);

    QString jsString() const;
    EventType type() const;

    //Event options:
    bool canBubble;
    bool cancelable;
    QString keyIdentifier;
    unsigned int keyLocation;
    bool ctrlKey;
    bool altKey;
    bool shiftKey;
    bool metaKey;
    bool altGraphKey;
    QString eventType;
private:
    mutable QString cachedJsString;

};

}

#endif // KEYBOARDEVENTPARAMETERS_H
