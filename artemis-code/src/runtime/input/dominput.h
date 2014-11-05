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

#ifndef DOMINPUT_H
#define DOMINPUT_H

#include <QSharedPointer>

#include "strategies/inputgenerator/targets/targetdescriptor.h"

#include "forms/forminputcollection.h"
#include "events/eventhandlerdescriptor.h"
#include "events/domelementdescriptor.h"
#include "events/eventparameters.h"

#include "model/stubeventexecutionstatistics.h"

#include "baseinput.h"

namespace artemis
{

class DomInput: public BaseInput
{

public:
    DomInput(EventHandlerDescriptorConstPtr handler,
             FormInputCollectionConstPtr formInput,
             EventParametersConstPtr params,
             TargetDescriptorConstPtr target,
             EventExecutionStatistics* execStat);


    void apply(ArtemisWebPagePtr page, QWebExecutionListener* webkitListener) const;
    BaseInputConstPtr getPermutation(const FormInputGeneratorConstPtr& formInputGenerator,
                                     const EventParameterGeneratorConstPtr& eventParameterGenerator,
                                     const TargetGeneratorConstPtr& targetGenerator,
                                     const ExecutionResultConstPtr& result) const;

    int hashCode() const;
    QString toString() const;
    TargetDescriptorConstPtr getTarget() const;

private:
    EventHandlerDescriptorConstPtr mEventHandler;
    FormInputCollectionConstPtr mFormInput;
    EventParametersConstPtr mEvtParams;
    TargetDescriptorConstPtr mTarget;
};

typedef QSharedPointer<const DomInput> DomInputConstPtr;

}

#endif // DOMINPUT_H
