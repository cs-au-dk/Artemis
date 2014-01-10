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

#ifndef EVENTHANDLERDESCRIPTOR_H
#define EVENTHANDLERDESCRIPTOR_H

#include <QObject>
#include <QString>
#include <QDebug>
#include <QSharedPointer>
#include <QWebElement>

#include "runtime/input/events/eventypes.h"
#include "domelementdescriptor.h"

namespace artemis
{

class EventHandlerDescriptor
{

public:
    EventHandlerDescriptor(QWebElement* element, QString name);

    inline QString getName() const {
        return mEventName;
    }

    inline DOMElementDescriptorConstPtr getDomElement() const {
        return mElement;
    }

    inline bool isInvalid() const {
        return mElement->isInvalid();
    }

    inline EventType getEventType() const {
        return getType(mEventName);
    }

    int hashCode() const;

    QString toString() const;

    QString xPathToElement() const;

    QDebug friend operator<<(QDebug dbg, const EventHandlerDescriptor& e);


private:
    DOMElementDescriptorConstPtr mElement;
    QString mEventName;
    QString mXPath;
};

typedef QSharedPointer<EventHandlerDescriptor> EventHandlerDescriptorPtr;
typedef QSharedPointer<const EventHandlerDescriptor> EventHandlerDescriptorConstPtr;

}

#endif // EVENTDESCRIPTOR_H
