/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
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

    KeyboardEventParameters(QString eventType, bool canBubble, bool cancelable,
                            QString keyIdentifier,  unsigned int keyLocation,
                            bool ctrlKey, bool altKey, bool shiftKey, bool metaKey, bool altGraphKey);

    QString getJsString() const;
    EventType getType() const;

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
