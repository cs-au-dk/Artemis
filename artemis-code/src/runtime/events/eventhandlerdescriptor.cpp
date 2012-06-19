/*
  Copyright 2011 Simon Holm Jensen. All rights reserved.
  
  Redistribution and use in source and binary forms, with or without modification, are
  permitted provided that the following conditions are met:
  
     1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.
  
     2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.
  
  THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
  WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  
  The views and conclusions contained in the software and documentation are those of the
  authors and should not be interpreted as representing official policies, either expressed
  or implied, of Simon Holm Jensen
*/
#include "eventhandlerdescriptor.h"

namespace artemis {

    EventHandlerDescriptor::EventHandlerDescriptor(QWebElement *elem, QString name)
    {
        this->event_name = name;
        this->element = new DOMElementDescriptor(elem);
    }

    EventHandlerDescriptor::EventHandlerDescriptor(const EventHandlerDescriptor &other) {
        this->event_name = other.event_name;
        this->element = new DOMElementDescriptor(*other.element);
    }

    EventHandlerDescriptor::~EventHandlerDescriptor() {
        delete element;
    }

    QString EventHandlerDescriptor::name() {
        return this->event_name;
    }

    DOMElementDescriptor EventHandlerDescriptor::dom_element() {
        return *element;
    }

    bool EventHandlerDescriptor::operator==(const EventHandlerDescriptor& other) const{
        return (event_name == other.event_name) && (element == other.element);
    }

    QDebug operator<<(QDebug dbg, const EventHandlerDescriptor &e) {
        dbg.nospace() << "(" + e.event_name << "," << e.element << ")";
        return dbg.space();
    }

    EventHandlerDescriptor &EventHandlerDescriptor::operator=(const EventHandlerDescriptor &other) {
        this->event_name = other.event_name;
        this->element = new DOMElementDescriptor(*other.element);
        return *this;
    }

    uint EventHandlerDescriptor::hashcode() const{
        return 19*qHash(event_name) + 7*qHash(element);
    }

    bool EventHandlerDescriptor::is_invalid() {
        return this->element->is_invalid();
    }
}

