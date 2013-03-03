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

#include "executionresult.h"

using namespace std;

namespace artemis
{

ExecutionResult::ExecutionResult()
{
    mModifiedDom = false;
    mStateHash = 0;
}

QString ExecutionResult::getPageContents() const
{
    return mPageContents;
}

QList<int> ExecutionResult::getAjaxCallbackHandlers() const
{
    return mAjaxCallbackHandlers;
}

QSet<QSharedPointer<const FormField> > ExecutionResult::getFormFields() const
{
    return mFormFields;
}

QSet<QSharedPointer<AjaxRequest> > ExecutionResult::getAjaxRequests() const
{
    return mAjaxRequest;
}

QList<EventHandlerDescriptor*> ExecutionResult::getEventHandlers() const
{
    return mEventHandlers;
}

QSet<QString> ExecutionResult::getEvalStrings()
{
    return mEvaledStrings;
}

long ExecutionResult::getPageStateHash() const
{
    return mStateHash;

}

bool ExecutionResult::isDomModified() const
{
    return mModifiedDom;
}

QList<QSharedPointer<Timer> > ExecutionResult::getTimers() const
{
    return mTimers.values();
}

QSet<QString> ExecutionResult::getJavascriptConstantsObservedForLastEvent() const
{
    return mJavascriptConstantsObservedForLastEvent;
}

void ExecutionResult::addJavascriptConstantObservedForLastEvent(QString constant) {
    mJavascriptConstantsObservedForLastEvent.insert(constant);
}

QDebug operator<<(QDebug dbg, const ExecutionResult& e)
{
    dbg.nospace() << "Event handlers: " << e.mEventHandlers << "\n";
    dbg.nospace() << "Form fields   : " << e.mFormFields << "\n";
    dbg.nospace() << "Modfied dom   : " << e.mModifiedDom << "\n";
    dbg.nospace() << "Ajax requests : " << e.mAjaxRequest << "\n";
    dbg.nospace() << "Evaled strings: " << e.mEvaledStrings;

    return dbg.space();
}

}
