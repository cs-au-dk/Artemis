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
#include "eventdescriptor.h"

namespace artemis {
    EventDescriptor::EventDescriptor(EventHandlerDescriptor &handler, FormInput &forms_state, EventParameters* params, TargetDescriptor* target)
    {
        Q_CHECK_PTR(params);

        this->event_handler = new EventHandlerDescriptor(handler);
        this->m_form_input = new FormInput(forms_state);
        this->evt_params = clone_eventparams(params);
        this->m_target = target;
    }

    EventDescriptor::EventDescriptor(const EventDescriptor &other) {
        this->event_handler = new EventHandlerDescriptor(*other.event_handler);
        this->m_form_input = new FormInput(*other.m_form_input);
        this->evt_params = clone_eventparams(other.evt_params);
        this->m_target = other.m_target;
    }

    EventDescriptor& EventDescriptor::operator=(const EventDescriptor &other) {
        delete this->event_handler;
        this->event_handler = new EventHandlerDescriptor(*other.event_handler);
        delete this->m_form_input;
        this->m_form_input = new FormInput(*other.m_form_input);
        delete this->evt_params;
        this->evt_params = clone_eventparams(other.evt_params);
        /* TODO TargetDescriptor Copy constructor */
        /*delete this->m_target;
        this->m_target = new TargetDescriptor(*other.m_target);*/
        this->m_target = other.m_target;
        return *this;
    }

    EventDescriptor::~EventDescriptor() {
        delete this->event_handler;
        delete this->m_form_input;
        delete this->evt_params;

        /* TODO TargetDescriptor Copy constructor */
        /*delete this->m_target;*/
    }

    TargetDescriptor* EventDescriptor::target() {
        return m_target;
    }

    EventHandlerDescriptor EventDescriptor::handler_descriptor() {
        return *event_handler;
    }

    FormInput EventDescriptor::form_input() {
        return *m_form_input;
    }

    EventParameters* EventDescriptor::event_params() {
        return evt_params;
    }

    bool EventDescriptor::operator==(const EventDescriptor& other) const {
        return (*event_handler == *other.event_handler) && (*other.m_form_input == *m_form_input) && (*other.evt_params == *evt_params);
    }

    QDebug  operator<<(QDebug dbg, const EventDescriptor &e) {
       dbg.nospace() << "{" << *e.event_handler << "," << *e.m_form_input << "," << *e.evt_params << "}";
       return dbg.space();
    }

    uint EventDescriptor::hashcode() const {
        return this->event_handler->hashcode()*23 + this->m_form_input->hashcode()*17 + evt_params->hashcode()*7;
    }
}
