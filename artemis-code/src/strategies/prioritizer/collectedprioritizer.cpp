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
#include "collectedprioritizer.h"

namespace artemis
{

CollectedPrioritizer::CollectedPrioritizer()
    : PrioritizerStrategy()
{
    strategies = new list<PrioritizerStrategy*>();
}

double CollectedPrioritizer::prioritize(QSharedPointer<const ExecutableConfiguration> conf, AppModelConstPtr appmodel)
{
    double priority = 1;
    list<PrioritizerStrategy*>::iterator iter;
    for(iter = strategies->begin(); iter != strategies->end(); iter++){
        priority = priority * (*iter)->prioritize(conf,appmodel);
    }
    return priority;
}

void CollectedPrioritizer::addPrioritizer(PrioritizerStrategy* strategy){
    strategies->push_front(strategy);
}

}
