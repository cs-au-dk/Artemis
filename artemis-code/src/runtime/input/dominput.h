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
#ifndef DOMINPUT_H
#define DOMINPUT_H

#include "strategies/inputgenerator/targets/targetdescriptor.h"

#include "forms/forminput.h"
#include "events/eventhandlerdescriptor.h"
#include "events/domelementdescriptor.h"
#include "events/eventparameters.h"

#include "baseinput.h"

namespace artemis
{

class DomInput: public BaseInput
{

public:
    DomInput(const EventHandlerDescriptor* handler, QSharedPointer<const FormInput> formInput,
             const EventParameters* params, const TargetDescriptor* target);

    void apply(ArtemisWebPagePtr page, QWebExecutionListener* webkitListener) const;
    QSharedPointer<const BaseInput> getPermutation(const QSharedPointer<const FormInputGenerator>& formInputGenerator,
                                                   const QSharedPointer<const EventParameterGenerator>& eventParameterGenerator,
                                                   TargetGenerator* targetGenerator,
                                                   QSharedPointer<const ExecutionResult> result) const;

    int hashCode() const;
    QString toString() const;

private:
    const EventHandlerDescriptor* mEventHandler;
    QSharedPointer<const FormInput> mFormInput;
    const EventParameters* mEvtParams;
    const TargetDescriptor* mTarget;
};

}

#endif // DOMINPUT_H
