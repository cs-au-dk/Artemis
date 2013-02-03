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

#include "assert.h"

#include "artemisglobals.h"

#include "runtime/input/dominput.h"

namespace artemis
{

DomInput::DomInput(const EventHandlerDescriptor* handler,
                   QSharedPointer<const FormInput> formInput,
                   const EventParameters* params,
                   const TargetDescriptor* target)
{
    // TODO change to auto ptr
    mEventHandler = handler;
    mFormInput = formInput;
    // TODO change to auto ptr
    mEvtParams = params;
    // TODO change to auto ptr
    mTarget = target;
}

void DomInput::apply(ArtemisWebPage* page, QWebExecutionListener* webkitListener) const
{
    QWebElement handler = mEventHandler->domElement()->getElement(page);
    QWebElement target = mTarget->get(page);

    QString jsInitEvent = mEvtParams->jsString();

    mFormInput->writeToPage(page);

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
        qDebug() << "Executing: " << jsInitEvent;

        QVariant result = target.evaluateJavaScript(jsInitEvent, DONT_MEASURE_COVERAGE);

        qDebug() << "Result: " << result;
    }
}

bool DomInput::isEqual(QSharedPointer<const BaseInput> other) const
{
    QSharedPointer<const DomInput> domInput = qSharedPointerDynamicCast<const DomInput>(other);

    if (domInput == NULL) {
        return false;
    }

    qFatal("Unimplemented function!");
    assert(false);

    // TODO Implement DomInput::isEqual
}

QSharedPointer<const BaseInput> DomInput::getPermutation(QSharedPointer<VariantsGenerator> variantsGenerator, TargetGenerator* targetGenerator) const
{
    EventParameters* newParams = variantsGenerator->generateEventParameters(NULL, mEventHandler);
    QSharedPointer<FormInput> newForm = variantsGenerator->generateFormFields(NULL, mFormInput->getFields());
    TargetDescriptor* target = targetGenerator->generateTarget(NULL, mEventHandler);
    EventHandlerDescriptor* newEventHandlerDescriptor = new EventHandlerDescriptor(NULL, mEventHandler);

    return QSharedPointer<const DomInput>(new DomInput(newEventHandlerDescriptor, newForm, newParams, target));
}

}
