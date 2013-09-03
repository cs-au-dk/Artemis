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

EventHandlerDescriptor::EventHandlerDescriptor(QWebElement* element, QString name) :
    mEventName(name)
{
    mElement = DOMElementDescriptorConstPtr(new DOMElementDescriptor(element));
}

int EventHandlerDescriptor::hashCode() const
{
    return qHash(this->mEventName) + 7 * this->mElement->hashCode();
}

QString EventHandlerDescriptor::toString() const
{
    return QString(mEventName + "@") + mElement->toString();
}

QDebug operator<<(QDebug dbg, const EventHandlerDescriptor& e)
{
    dbg.nospace() << "(" + e.mEventName << "," << e.mElement->toString() << ")";
    return dbg.space();
}

}

