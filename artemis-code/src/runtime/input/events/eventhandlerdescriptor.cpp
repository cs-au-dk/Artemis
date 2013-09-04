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
#include "eventhandlerdescriptor.h"

namespace artemis
{

EventHandlerDescriptor::EventHandlerDescriptor(QObject* parent, QWebElement* elem, QString name) : QObject(parent)
{
    this->eventName = name;
    this->element = DOMElementDescriptorConstPtr(new DOMElementDescriptor(elem));
}

EventHandlerDescriptor::EventHandlerDescriptor(QObject* parent, const EventHandlerDescriptor* other) : QObject(parent)
{
    this->eventName = other->eventName;
    this->element = other->element;
}

EventHandlerDescriptor::~EventHandlerDescriptor()
{
    delete element;
}

QString EventHandlerDescriptor::name() const
{
    return this->eventName;
}

EventType EventHandlerDescriptor::getEventType() const
{
    return getType(eventName);
}

bool EventHandlerDescriptor::isInvalid() const
{
    return this->element->isInvalid();
}

int EventHandlerDescriptor::hashCode() const
{
    return qHash(this->eventName) + 7 * this->element->hashCode();
}

QString EventHandlerDescriptor::toString() const
{
    return QString(eventName + "@") + element->toString();
}

QDebug operator<<(QDebug dbg, const EventHandlerDescriptor& e)
{
    dbg.nospace() << "(" + e.eventName << "," << e.element->toString() << ")";
    return dbg.space();
}

}

