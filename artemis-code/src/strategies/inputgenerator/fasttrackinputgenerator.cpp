/*
 * Copyright 2014 Aarhus University
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

#include "statistics/statsstorage.h"

#include "fasttrackinputgenerator.h"

namespace artemis
{

FasttrackInputGenerator::FasttrackInputGenerator(
        QObject* parent,
        FormInputGeneratorConstPtr formInputGenerator,
        QSharedPointer<const EventParameterGenerator> eventParameterInputGenerator,
        TargetGeneratorConstPtr targetGenerator,
        EventExecutionStatistics* execStat)
    : InputGeneratorStrategy(parent)
    , mFormInputGenerator(formInputGenerator)
    , mEventParameterGenerator(eventParameterInputGenerator)
    , mTargetGenerator(targetGenerator)
    , mExecStat(execStat)
{
}

QList<ExecutableConfigurationPtr> FasttrackInputGenerator::addNewConfigurations(
        ExecutableConfigurationConstPtr oldConfiguration,
        ExecutionResultConstPtr result)
{
    QList<ExecutableConfigurationPtr> newConfigurations;
    if (!oldConfiguration->isInitial()) return newConfigurations; // only allow one blast

    InputSequenceConstPtr inputSequence = oldConfiguration->getInputSequence();

    foreach (EventHandlerDescriptorConstPtr ee, result->getEventHandlers()) {

        EventType type = ee->getEventType();
        if (type == KEY_EVENT || type == MOUSE_EVENT || type == TOUCH_EVENT || type == BASE_EVENT) {

            FormInputCollectionPtr newForm = mFormInputGenerator->generateFormFields(result->getFormFields().toSet(), result);
            EventParametersConstPtr newParams = mEventParameterGenerator->generateEventParameters(ee);
            TargetDescriptorConstPtr target = mTargetGenerator->generateTarget(ee);

            DomInputConstPtr domInput = DomInputConstPtr(new DomInput(ee, newForm, newParams, target, mExecStat));
            inputSequence = inputSequence->extend(domInput);
        }
    }

    foreach (QSharedPointer<const Timer> timer, result->getTimers()) {
        BaseInputConstPtr newInput = QSharedPointer<const TimerInput>(new TimerInput(timer));
        inputSequence = inputSequence->extend(newInput);
    }

    foreach (int callbackId, result->getAjaxCallbackHandlers()) {
        BaseInputConstPtr newInput = QSharedPointer<const AjaxInput>(new AjaxInput(callbackId));
        inputSequence = inputSequence->extend(newInput);
    }

    Statistics::statistics()->accumulate("FastTrack::added-events", inputSequence->length());
    newConfigurations.append(ExecutableConfigurationPtr(new ExecutableConfiguration(
                                                            inputSequence,
                                                            oldConfiguration->getUrl())));

    return newConfigurations;
}

}
