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
#ifndef JAVASCRIPTSTATISTICS_H
#define JAVASCRIPTSTATISTICS_H

#include <QObject>
#include <QSharedPointer>
#include <QSet>
#include <QHash>

#include "runtime/input/baseinput.h"

namespace artemis {

class JavascriptStatistics : public QObject
{

    Q_OBJECT

public:
    JavascriptStatistics();

    void notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent);
    void notifyStartingLoad();

    QSet<QString> getPropertiesWritten(const QSharedPointer<const BaseInput>& input) const;
    QSet<QString> getPropertiesRead(const QSharedPointer<const BaseInput>& input) const;

private:

    // InputHash -> set<PropertyString>
    QHash<uint, QSet<QString>* > mPropertyReadSet;

    // InputHash -> set<PropertyString>
    QHash<uint, QSet<QString>* > mPropertyWriteSet;

    uint mInputBeingExecuted;

public slots:
    void slJavascriptPropertyRead(QString propertyName, intptr_t codeBlockID, intptr_t sourceID, QUrl url, int line);
    void slJavascriptPropertyWritten(QString propertyName, intptr_t codeBlockID, intptr_t sourceID, QUrl url, int line);

};

typedef QSharedPointer<JavascriptStatistics> JavascriptStatisticsPtr;

}

#endif // JAVASCRIPTSTATISTICS_H
