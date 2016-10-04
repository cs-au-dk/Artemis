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
        EventExecutionStatistics* execStat,
        int numberSameLength)
    : InputGeneratorStrategy(parent)
    , mFormInputGenerator(formInputGenerator)
    , mEventParameterGenerator(eventParameterInputGenerator)
    , mTargetGenerator(targetGenerator)
    , mExecStat(execStat)
    , mNumberSameLength(numberSameLength)
{
}

QList<QSharedPointer<ExecutableConfiguration> > RandomInputGenerator::addNewConfigurations(
        QSharedPointer<const ExecutableConfiguration> oldConfiguration,
        QSharedPointer<const ExecutionResult> result)
{

    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations;

    newConfigurations.append(insertSameLength(oldConfiguration, result));

    // TODO: This is a temporary working mode for Artemis, to simplify development and testing of the delegation support. We only explore single actions, not sequences of length >1.
    if (oldConfiguration->isInitial()) {
        newConfigurations.append(insertExtended(oldConfiguration, result));
    }

    return newConfigurations;
}

QList<ExecutableConfigurationPtr> RandomInputGenerator::insertSameLength(
        ExecutableConfigurationConstPtr oldConfiguration,
        ExecutionResultConstPtr result)
{
    QList<ExecutableConfigurationPtr> newConfigurations;
    if (oldConfiguration->isInitial()) return newConfigurations;

    InputSequenceConstPtr sequence = oldConfiguration->getInputSequence();
    BaseInputConstPtr last = sequence->getLast();

    for (int i = 0; i < mNumberSameLength; i++) {
        QSharedPointer<const BaseInput> newLast = last->getPermutation(mFormInputGenerator, mEventParameterGenerator, mTargetGenerator, result);
        if (newLast.isNull()) continue;

        QSharedPointer<const InputSequence> newSeq = sequence->replaceLast(newLast);
        QSharedPointer<ExecutableConfiguration> newConf = \
                QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(newSeq, oldConfiguration->getUrl()));
        newConfigurations.append(newConf);
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

            FormInputCollectionPtr newForm = mFormInputGenerator->generateFormFields(result->getFormFields().toSet(), result);
            EventParametersConstPtr newParams = mEventParameterGenerator->generateEventParameters(ee);
            TargetDescriptorConstPtr target = mTargetGenerator->generateTarget(ee);

            DomInputConstPtr domInput = DomInputConstPtr(new DomInput(ee, newForm, newParams, target, mExecStat));
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
