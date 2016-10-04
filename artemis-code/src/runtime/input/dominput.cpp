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

#include "assert.h"

#include "model/coverage/coveragelistener.h"

#include "dominput.h"

namespace artemis
{

DomInput::DomInput(EventHandlerDescriptorConstPtr handler,
                   FormInputCollectionConstPtr formInput,
                   EventParametersConstPtr params,
                   TargetDescriptorConstPtr target,
                   EventExecutionStatistics* execStat) :
    BaseInput(execStat),
    mEventHandler(handler),
    mFormInput(formInput),
    mEvtParams(params),
    mTarget(target)
{
}

void DomInput::apply(ArtemisWebPagePtr page, QWebExecutionListener*) const
{
    // Prepare forms

    mFormInput->writeToPage(page);

    // Trigger event

    QWebElement handler = mEventHandler->getDomElement()->getElement(page);
    QWebElement target = mTarget->get(page);

    if (handler.isNull() || target.isNull()) {
        qWarning() << "WARNING::Skipping event, event handler or target could not be found";

    } else if (mEvtParams->getType() == TOUCH_EVENT) {
        qWarning() << "WARNING::Skipping event, touch events are not supported!";

    } else {
        QString jsInitEvent = mEvtParams->getJsString();

        qDebug() << "Event Handler: " << handler.tagName() << " _ID: "
                 << handler.attribute(QString("id")) << " _Title: "
                 << handler.attribute(QString("title")) << "class: "
                 << handler.attribute(QString("class")) << "name: "
                 << handler.attribute(QString("name"));
        qDebug() << "Target: " << target.tagName() << " _ID: " << target.attribute(QString("id"))
                 << " _Title: " << target.attribute(QString("title")) << "class: "
                 << target.attribute(QString("class"));
        qDebug() << "Executing: " << jsInitEvent;
        mExecStat->registerEvent(EventTuple(mEventHandler, mEvtParams, mFormInput));
        QVariant result = target.evaluateJavaScript(jsInitEvent, DONT_MEASURE_COVERAGE);

        qDebug() << "Result: " << result;
    }
}

BaseInputConstPtr DomInput::getPermutation(const FormInputGeneratorConstPtr& formInputGenerator,
                                           const EventParameterGeneratorConstPtr& eventParameterGenerator,
                                           const TargetGeneratorConstPtr& targetGenerator,
                                           const ExecutionResultConstPtr& result) const
{
    EventParametersConstPtr newParams = eventParameterGenerator->permuteEventParameters(mEventHandler, mEvtParams, result);
    FormInputCollectionConstPtr newForm = formInputGenerator->permuteFormFields(mFormInput->getFields(), mFormInput, result);
    TargetDescriptorConstPtr target = targetGenerator->permuteTarget(mEventHandler, mTarget, result);

    if (!newParams.isNull() || !newForm.isNull() || !target.isNull()) {
        return DomInputConstPtr(new DomInput(
                                    mEventHandler,
                                    newForm.isNull() ? mFormInput : newForm,
                                    newParams.isNull() ? mEvtParams : newParams,
                                    target.isNull() ? mTarget : target,
                                    mExecStat));
    }

    return BaseInputConstPtr(NULL);

}

int DomInput::hashCode() const
{
    return 107 * mEventHandler->hashCode();
}

QString DomInput::toString() const
{

    return QString("DomInput(") + mEventHandler->toString() + QString(")");
}

TargetDescriptorConstPtr DomInput::getTarget() const
{
    return mTarget;
}

}
