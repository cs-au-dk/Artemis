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
#ifndef ABSTRACTPRIORITIZER_H
#define ABSTRACTPRIORITIZER_H

#include <QSharedPointer>

#include "runtime/browser/executionresult.h"
#include "runtime/worklist/worklist.h"
#include "runtime/appmodel.h"

namespace artemis
{

class PrioritizerStrategy
{
public:
    PrioritizerStrategy() {}
    virtual ~PrioritizerStrategy() {}

    virtual double prioritize(QSharedPointer<const ExecutableConfiguration> newConf,
                              AppModelConstPtr appmodel) = 0;
};

typedef QSharedPointer<PrioritizerStrategy> PrioritizerStrategyPtr;
typedef QSharedPointer<const PrioritizerStrategy> PrioritizerStrategyConstPtr;

}
#endif // ABSTRACTPRIORITIZER_H
