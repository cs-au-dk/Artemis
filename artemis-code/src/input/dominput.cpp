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

#include "artemisglobals.h"

#include "input/dominput.h"

namespace artemis
{

DomInput::DomInput(QObject* parent, const EventHandlerDescriptor &handler,
    const FormInput &formInput, EventParameters* params, TargetDescriptor* target) :
    BaseInput(parent)
{
    Q_CHECK_PTR(params);
    Q_CHECK_PTR(target);

    mEventHandler = handler;
    mFormInput = formInput;

    mEvtParams = params;
    //mEvtParams->setParent(this);

    mTarget = target;
    //mTarget->setParent(this);
}

void DomInput::apply(ArtemisWebPage *page, QWebExecutionListener *webkit_listener)
{
    QWebElement handler = this->mEventHandler.dom_element().get_element(page);
    QWebElement target = this->target()->get(page);
    QString js_init_event = this->event_params()->js_string();

    this->getFormInput().write_to_page(page);

    if (handler.isNull() || target.isNull()) {
        qDebug() << "WARNING::Skipping event, event handler or target could not be found";
    }
    else {
        qDebug() << "Event Handler: " << handler.tagName() << " _ID: "
            << handler.attribute(QString("id")) << " _Title: "
            << handler.attribute(QString("title")) << "class: "
            << handler.attribute(QString("class"));
        qDebug() << "Target: " << target.tagName() << " _ID: " << target.attribute(QString("id"))
            << " _Title: " << target.attribute(QString("title")) << "class: "
            << target.attribute(QString("class"));
        qDebug() << "Executing: " << js_init_event;

        QVariant result = target.evaluateJavaScript(js_init_event, DONT_MEASURE_COVERAGE);

        qDebug() << "Result: " << result;
    }
}

DomInput::~DomInput()
{
    //delete this->mEventHandler;
    //delete this->mFormInput;
    //delete this->mEvtParams;

    /* TODO TargetDescriptor Copy constructor */
    /*delete this->m_target;*/
}

TargetDescriptor* DomInput::target() const
{
    return mTarget;
}

EventHandlerDescriptor DomInput::getEventHandler() const
{
    return mEventHandler;
}

FormInput DomInput::getFormInput() const
{
    return mFormInput;
}

bool DomInput::isEqual(BaseInput *other)
{
    DomInput *domInput = dynamic_cast<DomInput *>(other);

    if (domInput == 0) {
        return false;
    }

    // TODO Implement DomInput::isEqual
}

EventParameters* DomInput::event_params() const
{
    return mEvtParams;
}
}
