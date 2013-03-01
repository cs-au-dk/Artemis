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
#ifndef ABSTRACTINPUTGENERATOR_H
#define ABSTRACTINPUTGENERATOR_H

#include <QObject>
#include <QList>
#include <QSharedPointer>

#include "runtime/browser/executionresult.h"
#include "runtime/worklist/worklist.h"
#include "runtime/browser/webkitexecutor.h"

namespace artemis
{

class InputGeneratorStrategy : public QObject
{
    Q_OBJECT
public:
    InputGeneratorStrategy(QObject* parent) : QObject(parent) {}
    virtual ~InputGeneratorStrategy() {}

    virtual QList<QSharedPointer<ExecutableConfiguration> > addNewConfigurations(QSharedPointer<const ExecutableConfiguration>, QSharedPointer<const ExecutionResult>) = 0;

};

}
#endif // ABSTRACTINPUTGENERATOR_H
