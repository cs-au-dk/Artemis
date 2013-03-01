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
#ifndef EVENTHANDLERDESCRIPTOR_H
#define EVENTHANDLERDESCRIPTOR_H

#include <QObject>
#include <QString>

#include "runtime/events/eventypes.h"
#include "domelementdescriptor.h"

namespace artemis
{

class EventHandlerDescriptor : public QObject
{
    Q_OBJECT

public:
    EventHandlerDescriptor(QObject* parent, QWebElement* elem = 0, QString name = QString());
    EventHandlerDescriptor(QObject* parent, const EventHandlerDescriptor* other);

    ~EventHandlerDescriptor();

    QString name() const;
    const DOMElementDescriptor* domElement() const;
    bool isInvalid() const;
    EventType getEventType() const;

    int hashCode() const;
    QString toString() const;

    QDebug friend operator<<(QDebug dbg, const EventHandlerDescriptor& e);


private:
    DOMElementDescriptor* element;
    QString eventName;

};
}

#endif // EVENTDESCRIPTOR_H
