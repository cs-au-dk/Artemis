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
#ifndef MOUSEEVENTPARAMETERS_H
#define MOUSEEVENTPARAMETERS_H

#include "eventparameters.h"

namespace artemis
{

class MouseEventParameters : public EventParameters
{
public:
    MouseEventParameters(QObject* parent, QString type, bool canBubble, bool cancelable,
                         int detail, int screenX, int screenY, int clientX, int clientY,
                         bool ctrlKey, bool altKey, bool  shiftKey, bool  metaKey,
                         int button);

    QString jsString() const;
    EventType type() const;

    bool canBubble;
    bool cancelable;
    int detail;
    int screenX;
    int screenY;
    int clientX;
    int clientY;
    bool ctrlKey;
    bool altKey;
    bool shiftKey;
    bool metaKey;
    int button;
    QString typeN;

private:
    mutable QString cachedJsString;

};

}
#endif // MOUSEEVENTPARAMETERS_H
