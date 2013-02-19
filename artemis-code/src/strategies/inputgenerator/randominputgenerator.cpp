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

#include <assert.h>
#include <typeinfo>

#include "runtime/events/eventypes.h"
#include "runtime/events/forms/forminput.h"
#include "runtime/input/baseinput.h"
#include "runtime/input/dominput.h"
#include "runtime/input/timerinput.h"
#include "runtime/input/ajaxinput.h"

#include "randominputgenerator.h"

namespace artemis
{

RandomInputGenerator::RandomInputGenerator(
        QObject* parent,
        QSharedPointer<const FormInputGenerator> formInputGenerator,
        QSharedPointer<const EventParameterGenerator> eventParameterInputGenerator,
        TargetGenerator* targetGenerator,
        int numberSameLength) :

    InputGeneratorStrategy(parent),
    mFormInputGenerator(formInputGenerator),
    mEventParameterGenerator(eventParameterInputGenerator)
{
    mTargetGenerator = targetGenerator;
    mTargetGenerator->setParent(this);

    mNumberSameLength = numberSameLength;

}

QList<QSharedPointer<ExecutableConfiguration> > RandomInputGenerator::addNewConfigurations(
        QSharedPointer<const ExecutableConfiguration> configuration,
        QSharedPointer<const ExecutionResult> result)
{

    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations;

    newConfigurations.append(insertSameLength(configuration, result));
    newConfigurations.append(insertExtended(configuration, result));

    return newConfigurations;
}

QList<QSharedPointer<ExecutableConfiguration> > RandomInputGenerator::insertSameLength(
        QSharedPointer<const ExecutableConfiguration> oldConfiguration,
        QSharedPointer<const ExecutionResult>)
{
    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations;

    QSharedPointer<const InputSequence> sequence = oldConfiguration->getInputSequence();

    if (sequence->isEmpty()) {
        return newConfigurations;
    }

    QSharedPointer<const BaseInput> last = sequence->getLast();

    for (int i = 0; i < mNumberSameLength; i++) {
        QSharedPointer<const BaseInput> newLast = last->getPermutation(mFormInputGenerator, mEventParameterGenerator, mTargetGenerator);

        QSharedPointer<const InputSequence> newSeq = sequence->replaceLast(newLast);
        QSharedPointer<ExecutableConfiguration> newConf = \
                QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(newSeq, oldConfiguration->getUrl()));
        newConfigurations.append(newConf);

        /**
         * // TODO
         *
         * The above code will generate duplicates of the same sequence over time, as the variants generator can repeat already
         * used parameters. Is this a good way to extend our test sequences? And if so should we put in some "isEqual"-ish check
         * to avoid duplications?
         */
    }

    return newConfigurations;
}

QList<QSharedPointer<ExecutableConfiguration> > RandomInputGenerator::insertExtended(
        QSharedPointer<const ExecutableConfiguration> oldConfiguration,
        QSharedPointer<const ExecutionResult> result)
{
    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations;

    foreach (EventHandlerDescriptor* ee, result->getEventHandlers()) {
        EventParameters* newParams = mEventParameterGenerator->generateEventParameters(NULL, ee);
        TargetDescriptor* target = mTargetGenerator->generateTarget(NULL, ee);
        QSharedPointer<FormInput> newForm = mFormInputGenerator->generateFormFields(NULL, result->getFormFields());
        QSharedPointer<const DomInput> domInput = QSharedPointer<const DomInput>(new DomInput(ee, newForm, newParams, target));

        QSharedPointer<const InputSequence> newInputSequence = oldConfiguration->getInputSequence()->extend(domInput);

        QSharedPointer<ExecutableConfiguration> newConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(newInputSequence, oldConfiguration->getUrl()));

        newConfigurations.append(newConfiguration);
    }

    foreach (QSharedPointer<const Timer> timer, result->getTimers()) {
        QSharedPointer<const BaseInput> newInput = QSharedPointer<const TimerInput>(new TimerInput(timer));

        QSharedPointer<const InputSequence> newSeq = oldConfiguration->getInputSequence()->extend(newInput);

        QSharedPointer<ExecutableConfiguration> newConf = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(newSeq, oldConfiguration->getUrl()));

        newConfigurations.append(newConf);
    }

    foreach (int callbackId, result->getAjaxCallbackHandlers()) {
        QSharedPointer<const BaseInput> newInput = QSharedPointer<const AjaxInput>(new AjaxInput(callbackId));

        QSharedPointer<const InputSequence> newSequence = oldConfiguration->getInputSequence()->extend(newInput);

        QSharedPointer<ExecutableConfiguration> newConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(newSequence,
                oldConfiguration->getUrl()));

        newConfigurations.append(newConfiguration);
    }

    return newConfigurations;
}

}
