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
#ifndef EXECUTABLECONFIGURATION_H
#define EXECUTABLECONFIGURATION_H

#include <QUrl>
#include <QSharedPointer>

#include "input/inputsequence.h"
#include "runtime/events/forms/forminput.h"

namespace artemis
{

class ExecutableConfiguration
{

public:
    ExecutableConfiguration(QSharedPointer<const InputSequence> sequence, const QUrl url);

    bool isInitial() const;
    const QUrl getUrl() const;
    QSharedPointer<const InputSequence> getInputSequence() const;

    QString toString() const;

private:
    const QUrl mUrl;
    QSharedPointer<const InputSequence> mSequence;
};

typedef QSharedPointer<ExecutableConfiguration> ExecutableConfigurationPtr;
typedef QSharedPointer<const ExecutableConfiguration> ExecutableConfigurationConstPtr;
}

#endif // EXECUTABLECONFIGURATION_H
