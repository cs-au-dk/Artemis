/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <assert.h>
#include <typeinfo>

#include "runtime/input/events/eventypes.h"
#include "runtime/input/forms/forminputcollection.h"
#include "runtime/input/baseinput.h"
#include "runtime/input/dominput.h"
#include "runtime/input/timerinput.h"
#include "runtime/input/ajaxinput.h"
#include "runtime/input/events/unknowneventparameters.h"

#include "randominputgenerator.h"

namespace artemis
{

RandomInputGenerator::RandomInputGenerator(
        QObject* parent,
        FormInputGeneratorConstPtr formInputGenerator,
        QSharedPointer<const EventParameterGenerator> eventParameterInputGenerator,
        TargetGeneratorConstPtr targetGenerator,
        int numberSameLength) :

    InputGeneratorStrategy(parent),
    mFormInputGenerator(formInputGenerator),
    mEventParameterGenerator(eventParameterInputGenerator),
    mTargetGenerator(targetGenerator),
    mNumberSameLength(numberSameLength)
{
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

QList<ExecutableConfigurationPtr> RandomInputGenerator::insertSameLength(
        ExecutableConfigurationConstPtr oldConfiguration,
        ExecutionResultConstPtr result)
{
    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations;

    QSharedPointer<const InputSequence> sequence = oldConfiguration->getInputSequence();

    if (sequence->isEmpty()) {
        return newConfigurations;
    }

    QSharedPointer<const BaseInput> last = sequence->getLast();

    for (int i = 0; i < mNumberSameLength; i++) {
        QSharedPointer<const BaseInput> newLast = last->getPermutation(mFormInputGenerator, mEventParameterGenerator, mTargetGenerator, result);

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

QList<ExecutableConfigurationPtr> RandomInputGenerator::insertExtended(
        ExecutableConfigurationConstPtr oldConfiguration,
        ExecutionResultConstPtr result)
{
    QList<ExecutableConfigurationPtr> newConfigurations;

    foreach (EventHandlerDescriptorConstPtr ee, result->getEventHandlers()) {

        EventType type = ee->getEventType();

        // TODO what should we do with all of the other types of events?
        if (type == KEY_EVENT || type == MOUSE_EVENT || type == TOUCH_EVENT || type == BASE_EVENT) {

            FormInputCollectionPtr newForm = mFormInputGenerator->generateFormFields(result->getFormFields(), result);
            EventParametersConstPtr newParams = mEventParameterGenerator->generateEventParameters(ee);
            TargetDescriptorConstPtr target = mTargetGenerator->generateTarget(ee);

            DomInputConstPtr domInput = DomInputConstPtr(new DomInput(ee, newForm, newParams, target));
            InputSequenceConstPtr newInputSequence = oldConfiguration->getInputSequence()->extend(domInput);

            ExecutableConfigurationPtr newConfiguration = ExecutableConfigurationPtr(new ExecutableConfiguration(newInputSequence, oldConfiguration->getUrl()));

            newConfigurations.append(newConfiguration);
        }

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
