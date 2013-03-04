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

void DomInput::apply(ArtemisWebPagePtr page, QWebExecutionListener* webkitListener) const
{
    QWebElement handler = mEventHandler->domElement()->getElement(page);
    QWebElement target = mTarget->get(page);

    QString jsInitEvent = mEvtParams->jsString();

    mFormInput->writeToPage(page);

    if (handler.isNull() || target.isNull()) {
        qWarning() << "WARNING::Skipping event, event handler or target could not be found";
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

QSharedPointer<const BaseInput> DomInput::getPermutation(const QSharedPointer<const FormInputGenerator>& formInputGenerator,
                                                         const QSharedPointer<const EventParameterGenerator>& eventParameterGenerator,
                                                         TargetGenerator* targetGenerator,
                                                         QSharedPointer<const ExecutionResult> result) const
{
    EventParameters* newParams = eventParameterGenerator->generateEventParameters(NULL, mEventHandler);
    QSharedPointer<FormInput> newForm = formInputGenerator->generateFormFields(NULL, mFormInput->getFields(), result);
    TargetDescriptor* target = targetGenerator->generateTarget(NULL, mEventHandler);
    EventHandlerDescriptor* newEventHandlerDescriptor = new EventHandlerDescriptor(NULL, mEventHandler);

    return QSharedPointer<const DomInput>(new DomInput(newEventHandlerDescriptor, newForm, newParams, target));
}

int DomInput::hashCode() const
{
    return 107 * mEventHandler->hashCode();
}

QString DomInput::toString() const
{

    return QString("DomInput(") + mEventHandler->toString() + QString(")");
}

}
