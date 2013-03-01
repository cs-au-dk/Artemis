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
#include <iostream>

#include "statistics/statsstorage.h"

#include "javascriptstatistics.h"

namespace artemis {

JavascriptStatistics::JavascriptStatistics() :
    QObject(NULL),
    mInputBeingExecuted(0)
{
}

void JavascriptStatistics::notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent)
{
    mInputBeingExecuted = inputEvent->hashCode();

    if (!mPropertyReadSet.contains(mInputBeingExecuted)) {
        mPropertyReadSet.insert(mInputBeingExecuted, new QSet<QString>());
    }

    if (!mPropertyWriteSet.contains(mInputBeingExecuted)) {
        mPropertyWriteSet.insert(mInputBeingExecuted, new QSet<QString>());
    }
}

void JavascriptStatistics::slJavascriptPropertyRead(QString propertyName)
{
    statistics()->accumulate("WebKit::readproperties", 1);

    if (mInputBeingExecuted != 0) {
        mPropertyReadSet.value(mInputBeingExecuted)->insert(propertyName);
    }
}

void JavascriptStatistics::slJavascriptPropertyWritten(QString propertyName)
{
    statistics()->accumulate("WebKit::writtenproperties", 1);

    if (mInputBeingExecuted != 0) {
        mPropertyWriteSet.value(mInputBeingExecuted)->insert(propertyName);
    }
}

QSet<QString> JavascriptStatistics::getPropertiesWritten(const QSharedPointer<const BaseInput>& input) const
{
    uint hashcode = input->hashCode();

    if (mPropertyWriteSet.contains(hashcode)) {
        return *mPropertyWriteSet.value(hashcode);
    }

    return QSet<QString>();
}

QSet<QString> JavascriptStatistics::getPropertiesRead(const QSharedPointer<const BaseInput>& input) const
{
    uint hashcode = input->hashCode();

    if (mPropertyReadSet.contains(hashcode)) {
        return *mPropertyReadSet.value(hashcode);
    }

    return QSet<QString>();
}

}
